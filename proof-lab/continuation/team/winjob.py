"""Windows worker-owned process-tree containment; no providers or import side effects.

Call attach_worker_job before starting any child process or external provider work.
The noninheritable handle is deliberately retained until OS process exit. Closing
it early would kill this worker and its descendants; this is not a context manager.
"""
from __future__ import annotations
from dataclasses import dataclass
import ctypes
import os

KILL_ON_JOB_CLOSE = 0x2000
BREAKAWAY_FLAGS = 0x800 | 0x1000
HANDLE_FLAG_INHERIT = 1
EXTENDED_LIMIT_INFORMATION = 9

class JobContainmentError(RuntimeError):
    pass

class _BasicLimits(ctypes.Structure):
    _fields_ = [
        ('PerProcessUserTimeLimit', ctypes.c_int64),
        ('PerJobUserTimeLimit', ctypes.c_int64),
        ('LimitFlags', ctypes.c_uint32),
        ('MinimumWorkingSetSize', ctypes.c_size_t),
        ('MaximumWorkingSetSize', ctypes.c_size_t),
        ('ActiveProcessLimit', ctypes.c_uint32),
        ('Affinity', ctypes.c_size_t),
        ('PriorityClass', ctypes.c_uint32),
        ('SchedulingClass', ctypes.c_uint32),
    ]

class _IOCounters(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint64) for name in (
        'ReadOperationCount', 'WriteOperationCount', 'OtherOperationCount',
        'ReadTransferCount', 'WriteTransferCount', 'OtherTransferCount')]

class _ExtendedLimits(ctypes.Structure):
    _fields_ = [('BasicLimitInformation', _BasicLimits), ('IoInfo', _IOCounters),
                ('ProcessMemoryLimit', ctypes.c_size_t), ('JobMemoryLimit', ctypes.c_size_t),
                ('PeakProcessMemoryUsed', ctypes.c_size_t), ('PeakJobMemoryUsed', ctypes.c_size_t)]

class _WindowsAPI:
    def __init__(self):
        if os.name != 'nt':
            raise JobContainmentError('windows_required')
        k = ctypes.WinDLL('kernel32', use_last_error=True)
        handle, boolean, dword = ctypes.c_void_p, ctypes.c_int, ctypes.c_uint32
        k.CreateJobObjectW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p]
        k.CreateJobObjectW.restype = handle
        k.SetHandleInformation.argtypes = [handle, dword, dword]
        k.SetHandleInformation.restype = boolean
        k.GetHandleInformation.argtypes = [handle, ctypes.POINTER(dword)]
        k.GetHandleInformation.restype = boolean
        k.SetInformationJobObject.argtypes = [handle, ctypes.c_int, ctypes.c_void_p, dword]
        k.SetInformationJobObject.restype = boolean
        k.QueryInformationJobObject.argtypes = [handle, ctypes.c_int, ctypes.c_void_p, dword, ctypes.POINTER(dword)]
        k.QueryInformationJobObject.restype = boolean
        k.GetCurrentProcess.argtypes = []
        k.GetCurrentProcess.restype = handle
        k.AssignProcessToJobObject.argtypes = [handle, handle]
        k.AssignProcessToJobObject.restype = boolean
        k.CloseHandle.argtypes = [handle]
        k.CloseHandle.restype = boolean
        self.k = k

    @staticmethod
    def _failure(operation):
        raise JobContainmentError(operation + '_failed_winerror_' + str(ctypes.get_last_error()))

    def create(self):
        handle = self.k.CreateJobObjectW(None, None)
        if not handle:
            self._failure('create_job')
        return int(handle)

    def configure(self, handle):
        if not self.k.SetHandleInformation(handle, HANDLE_FLAG_INHERIT, 0):
            self._failure('disable_job_inheritance')
        flags = ctypes.c_uint32()
        if not self.k.GetHandleInformation(handle, ctypes.byref(flags)):
            self._failure('read_job_handle_flags')
        if flags.value & HANDLE_FLAG_INHERIT:
            raise JobContainmentError('job_handle_inheritable')
        limits = _ExtendedLimits()
        limits.BasicLimitInformation.LimitFlags = KILL_ON_JOB_CLOSE
        if not self.k.SetInformationJobObject(handle, EXTENDED_LIMIT_INFORMATION,
                                              ctypes.byref(limits), ctypes.sizeof(limits)):
            self._failure('set_job_limits')
        found = _ExtendedLimits()
        if not self.k.QueryInformationJobObject(handle, EXTENDED_LIMIT_INFORMATION,
                                                ctypes.byref(found), ctypes.sizeof(found), None):
            self._failure('read_job_limits')
        flags = found.BasicLimitInformation.LimitFlags
        if not (flags & KILL_ON_JOB_CLOSE) or flags & BREAKAWAY_FLAGS:
            raise JobContainmentError('job_limits_not_containing')

    def assign_current(self, handle):
        if not self.k.AssignProcessToJobObject(handle, self.k.GetCurrentProcess()):
            self._failure('assign_current_worker')

    def close_unassigned(self, handle):
        self.k.CloseHandle(handle)

@dataclass(frozen=True)
class WorkerJob:
    pid: int
    handle: int
    contained: bool = True


def _attach_kernel(api, pid):
    handle = api.create()
    try:
        api.configure(handle)
        api.assign_current(handle)
    except BaseException:
        # Assignment failed: this job has no members, so closing cannot target
        # another process. Never close a successfully assigned worker job here.
        api.close_unassigned(handle)
        raise
    return WorkerJob(pid=pid, handle=handle)

_worker_job = None

def attach_worker_job():
    """Attach only this process, before external work; fail closed on any error.

    Existing/nested host jobs are not altered or escaped. The handle is retained
    globally and never duplicated/inherited. Worker exit closes it in the OS,
    terminating this job's descendants. Repeated calls in the same worker are
    idempotent; no process is reopened or terminated by a recorded PID.
    """
    global _worker_job
    if _worker_job is not None:
        if _worker_job.pid != os.getpid():
            raise JobContainmentError('worker_identity_changed')
        return _worker_job
    _worker_job = _attach_kernel(_WindowsAPI(), os.getpid())
    return _worker_job
