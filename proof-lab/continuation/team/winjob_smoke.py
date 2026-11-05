"""Harmless Windows smoke: terminate one owned worker and observe child exit.

No provider, key, ledger, or unrelated process access. Only a 30-second sleeping
child is created. Parent retains its own Popen worker handle; the descendant's
known live handle is opened for synchronization only, never for termination.
"""
import ctypes
import json
import os
import queue
import subprocess
import sys
import threading
import time
from pathlib import Path
from continuation.team.winjob import attach_worker_job

ROOT = Path(__file__).resolve().parents[2]

def child():
    attach_worker_job()
    sleeper = subprocess.Popen([sys.executable, '-B', '-c', 'import time; time.sleep(30)'],
        cwd=ROOT, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        creationflags=subprocess.CREATE_NO_WINDOW, close_fds=True)
    print(json.dumps({'contained': True, 'descendant_pid': sleeper.pid}), flush=True)
    while True: time.sleep(.1)

def smoke():
    if os.name != 'nt': raise RuntimeError('windows_required')
    k = ctypes.WinDLL('kernel32', use_last_error=True)
    k.OpenProcess.argtypes = [ctypes.c_uint32, ctypes.c_int, ctypes.c_uint32]
    k.OpenProcess.restype = ctypes.c_void_p
    k.WaitForSingleObject.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
    k.WaitForSingleObject.restype = ctypes.c_uint32
    k.CloseHandle.argtypes = [ctypes.c_void_p]
    k.CloseHandle.restype = ctypes.c_int
    worker = subprocess.Popen([sys.executable, '-B', '-m', 'continuation.team.winjob_smoke', '--child'],
        cwd=ROOT, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding='utf-8', creationflags=subprocess.CREATE_NO_WINDOW, close_fds=True)
    mailbox = queue.Queue(maxsize=1)
    reader = threading.Thread(target=lambda: mailbox.put(worker.stdout.readline()), daemon=True)
    reader.start()
    descendant = None
    try:
        line = mailbox.get(timeout=10)
        record = json.loads(line)
        if record.get('contained') is not True or type(record.get('descendant_pid')) is not int:
            raise RuntimeError('invalid_owned_child_handshake')
        descendant = k.OpenProcess(0x00100000, False, record['descendant_pid'])  # SYNCHRONIZE only
        if not descendant or k.WaitForSingleObject(descendant, 0) != 0x102:
            raise RuntimeError('owned_descendant_not_running')
        started = time.monotonic()
        worker.terminate()  # Popen's original process handle, not a PID lookup.
        worker.wait(timeout=5)
        if k.WaitForSingleObject(descendant, 5000) != 0:
            raise RuntimeError('owned_descendant_did_not_exit_with_job')
        result = {'status': 'PASS', 'worker_exited': True, 'descendant_exited': True,
                  'elapsed_after_stop_seconds': round(time.monotonic()-started, 6),
                  'scope': 'Only one owned harmless worker and its sleeping child; no providers or ledger.'}
        print(json.dumps(result), flush=True)
        return result
    finally:
        if worker.poll() is None:
            worker.terminate()
            worker.wait(timeout=5)
        if descendant: k.CloseHandle(descendant)
        reader.join(timeout=1)
        if not reader.is_alive(): worker.stdout.close()
        worker.stderr.close()

if __name__ == '__main__':
    if sys.argv[1:] == ['--child']: child()
    elif not sys.argv[1:]: smoke()
    else: raise SystemExit('unknown arguments')
