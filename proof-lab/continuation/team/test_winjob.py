"""Offline ordering and fail-closed tests; no providers or real process mutation."""
import ctypes
import unittest
from unittest.mock import patch
from continuation.team import winjob

class FakeAPI:
    def __init__(self, fail=None):
        self.fail, self.calls = fail, []
    def _call(self, name):
        self.calls.append(name)
        if self.fail == name:
            raise winjob.JobContainmentError(name)
    def create(self):
        self._call('create'); return 77
    def configure(self, handle):
        assert handle == 77
        self._call('configure')
    def assign_current(self, handle):
        assert handle == 77
        self._call('assign_current')
    def close_unassigned(self, handle):
        assert handle == 77
        self._call('close_unassigned')

class WinJobTests(unittest.TestCase):
    def test_order_and_no_close_after_success(self):
        api = FakeAPI()
        result = winjob._attach_kernel(api, 123)
        self.assertEqual(api.calls, ['create', 'configure', 'assign_current'])
        self.assertEqual((result.pid, result.handle, result.contained), (123, 77, True))
    def test_create_failure_does_not_close_an_unowned_handle(self):
        api = FakeAPI('create')
        with self.assertRaises(winjob.JobContainmentError): winjob._attach_kernel(api, 123)
        self.assertEqual(api.calls, ['create'])
    def test_configuration_failure_never_assigns_and_closes_only_own_job(self):
        api = FakeAPI('configure')
        with self.assertRaises(winjob.JobContainmentError): winjob._attach_kernel(api, 123)
        self.assertEqual(api.calls, ['create', 'configure', 'close_unassigned'])
    def test_nested_assignment_failure_fails_closed(self):
        api = FakeAPI('assign_current')
        with self.assertRaises(winjob.JobContainmentError): winjob._attach_kernel(api, 123)
        self.assertEqual(api.calls, ['create', 'configure', 'assign_current', 'close_unassigned'])
    def test_public_attach_is_idempotent_without_extra_os_calls(self):
        api = FakeAPI()
        with patch.object(winjob, '_worker_job', None), patch.object(winjob, '_WindowsAPI', return_value=api), patch.object(winjob.os, 'getpid', return_value=123):
            first = winjob.attach_worker_job()
            self.assertIs(winjob.attach_worker_job(), first)
        self.assertEqual(api.calls, ['create', 'configure', 'assign_current'])
    def test_reused_global_identity_refuses_instead_of_adopting(self):
        with patch.object(winjob, '_worker_job', winjob.WorkerJob(123, 77)), patch.object(winjob.os, 'getpid', return_value=456):
            with self.assertRaises(winjob.JobContainmentError): winjob.attach_worker_job()
    def test_structure_layout_matches_windows_pointer_width(self):
        expected = 144 if ctypes.sizeof(ctypes.c_void_p) == 8 else 112
        self.assertEqual(ctypes.sizeof(winjob._ExtendedLimits), expected)
        self.assertEqual(winjob.KILL_ON_JOB_CLOSE & winjob.BREAKAWAY_FLAGS, 0)
        self.assertEqual(winjob._ExtendedLimits().BasicLimitInformation.LimitFlags, 0)

if __name__ == '__main__': unittest.main()
