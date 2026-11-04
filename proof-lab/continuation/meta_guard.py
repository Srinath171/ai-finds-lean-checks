"""One bounded continuation job; no global expiry, no calls during import.

Reuses a private hash-pinned client instance. Existing ledgers and old job
folders are never initialized, reset, adopted, or automatically retried.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from decimal import Decimal
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import sys
import time
import uuid
from budget import BudgetLedger, BudgetError

ROOT = Path(__file__).resolve().parents[1]
CONT_ROOT = ROOT / 'continuation'
LEDGER_PATH = ROOT / 'logs' / 'spending.json'
CLIENT_SOURCE = ROOT / 'frontier' / 'background_meta.py'
CLIENT_SHA256_LF = '730551c9ff0f2215e207df0cfb599506e86863bfcfa88b18f76c78eddd4fcaed'
CAPS = {'meta': '115', 'claude': '40'}
JOB_RE = re.compile(r'[a-z0-9][a-z0-9_-]{0,63}\Z')
MAX_JOB_SECONDS = 1200


class ContinuationError(RuntimeError):
    pass


def _number(value):
    return type(value) in (int, float) and math.isfinite(value)


def _source_check():
    raw = CLIENT_SOURCE.read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    if hashlib.sha256(raw).hexdigest() != CLIENT_SHA256_LF:
        raise ContinuationError('frozen_client_changed')


def _read(path):
    def pairs(items):
        data = {}
        for key, value in items:
            if key in data:
                raise ContinuationError('duplicate_metadata_key')
            data[key] = value
        return data
    with path.open('rb') as handle:
        raw = handle.read(32769)
    if len(raw) > 32768:
        raise ContinuationError('binding_too_large')
    try:
        return json.loads(raw.decode('utf-8'), object_pairs_hook=pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(ValueError()))
    except (UnicodeError, ValueError):
        raise ContinuationError('invalid_binding_json') from None


def _exclusive(path, data):
    with path.open('x', encoding='utf-8') as handle:
        json.dump(data, handle, sort_keys=True, indent=2, allow_nan=False)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())


def _local(path):
    if path.resolve() != path.absolute() or not path.resolve().is_relative_to(ROOT.resolve()):
        raise ContinuationError('path_not_local_to_project')
    return path


def _binding(path, job):
    data = _read(_local(path))
    keys = {'version', 'kind', 'job_name', 'job_id', 'prompt_sha256', 'created_epoch',
            'deadline_epoch', 'max_job_seconds', 'poll_interval', 'max_requests',
            'caps_usd', 'client_sha256_lf'}
    if (type(data) is not dict or set(data) != keys or type(data['version']) is not int
            or data['version'] != 1 or data['kind'] != 'bounded-meta-continuation'
            or data['job_name'] != job or data['caps_usd'] != CAPS
            or data['client_sha256_lf'] != CLIENT_SHA256_LF
            or type(data['job_id']) is not str or not re.fullmatch(r'[0-9a-f]{32}', data['job_id'])
            or type(data['prompt_sha256']) is not str or not re.fullmatch(r'[0-9a-f]{64}', data['prompt_sha256'])
            or type(data['max_job_seconds']) is not int or not 30 <= data['max_job_seconds'] <= MAX_JOB_SECONDS
            or not _number(data['created_epoch']) or data['created_epoch'] < 0
            or not _number(data['deadline_epoch'])
            or data['deadline_epoch'] != data['created_epoch'] + data['max_job_seconds']
            or not _number(data['poll_interval']) or not 0 < data['poll_interval'] <= 15
            or type(data['max_requests']) is not int or not 2 <= data['max_requests'] <= 250):
        raise ContinuationError('invalid_immutable_job_binding')
    return data


def _bound_state(state, binding):
    expected = {'job_id': binding['job_id'], 'prompt_sha256': binding['prompt_sha256'],
                'started_epoch': binding['created_epoch'], 'deadline_epoch': binding['deadline_epoch'],
                'max_job_seconds': binding['max_job_seconds'], 'poll_interval': binding['poll_interval'],
                'max_requests': binding['max_requests']}
    if type(state) is not dict or any(type(state.get(k)) is bool or state.get(k) != v
                                      for k, v in expected.items()):
        raise ContinuationError('old_or_unbound_job_state')


class ExistingLedger(BudgetLedger):
    """Existing-only accounting. Both authorization caps checked inside locks."""
    def __init__(self, path=None):
        self.path = Path(LEDGER_PATH if path is None else path).resolve()
        self.lock_path = self.path.with_name(self.path.name + '.lock')
        self.lock_timeout = 2.0
        self.status()

    def _read(self):
        state = super()._read()
        if any(Decimal(state['caps_usd'][p]) > Decimal(CAPS[p]) for p in CAPS):
            raise BudgetError('provider_cap_exceeds_continuation_authorization')
        return state


def _client(binding_path, binding, output, wall, mono, sleep, process_end, transport):
    _source_check()
    spec = importlib.util.spec_from_file_location('_continuation_private_meta_' + binding['job_id'], CLIENT_SOURCE)
    client = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(client)
    client.HARD_DEADLINE = binding['deadline_epoch']
    client.HARD_DEADLINE_UTC = datetime.fromtimestamp(binding['deadline_epoch'], timezone.utc).isoformat()
    client.LEDGER_PATH, client.ROOT = LEDGER_PATH, ROOT
    client.ExistingMetaLedger = ExistingLedger

    def check_binding():
        if _binding(binding_path, binding['job_name']) != binding:
            raise ContinuationError('job_binding_changed')

    def stopped():
        return (CONT_ROOT / 'STOP').exists() or (output / 'STOP').exists()

    def sync_stop():
        if (CONT_ROOT / 'STOP').exists() and not (output / 'STOP').exists():
            try:
                _exclusive(output / 'STOP', {'reason': 'continuation_stop'})
            except FileExistsError:
                pass

    base = client._Session
    class GuardedSession(base):
        def save(self):
            check_binding()
            if (self.state.get('phase') == 'PREPARING' and self.state.get('reservation_id') is None
                    and self.state.get('response_id') is None and self.state.get('request_count') == 0
                    and not (output / 'state.json').exists()):
                # Binding is created exclusively before any key lookup or reservation.
                self.state['job_id'] = binding['job_id']
                self.state['started_epoch'] = binding['created_epoch']
            _bound_state(self.state, binding)
            return super().save()

        def remaining(self):
            return min(super().remaining(), process_end - mono())

        def get_key(self):
            if self.state is None and stopped():
                raise client.SafeError('deadline_or_stop_before_submission')
            return super().get_key()

        def request(self, kind, payload=None):
            check_binding()
            sync_stop()
            if kind != 'cancel' and stopped():
                raise client.SafeError('stop_before_transport')
            with self.ledger._locked():
                self.ledger._read()
            return super().request(kind, payload)

        def drive(self):
            sync_stop()
            return super().drive()

    client._Session = GuardedSession
    original_validate = client._validate_state
    def validate(state, ledger, folder):
        check_binding()
        _bound_state(state, binding)
        return original_validate(state, ledger, folder)
    client._validate_state = validate
    actual_transport = transport or client.http_transport
    def guarded_transport(method, url, payload, timeout, key):
        check_binding()
        sync_stop()
        cancelling = method == 'POST' and url.endswith('/cancel')
        if not cancelling and stopped():
            raise client.SafeError('stop_before_transport')
        ledger = ExistingLedger()
        with ledger._locked():
            ledger._read()
        # Lock waits can consume the deadline or allow a STOP to arrive.
        sync_stop()
        if not cancelling and stopped():
            raise client.SafeError('stop_before_transport')
        now, tick = wall(), mono()
        if not _number(now) or not _number(tick) or now < binding['created_epoch'] - 1:
            raise client.SafeError('clock_regression')
        remaining = min(binding['deadline_epoch'] - now, process_end - tick)
        remaining -= 0 if cancelling else client.CANCEL_MARGIN
        if remaining <= 0:
            raise client.SafeError('deadline')
        return actual_transport(method, url, payload, min(timeout, remaining, 30), key)

    def guarded_sleep(seconds):
        sync_stop()
        if not stopped():
            sleep(min(seconds, max(0, process_end - mono())))
        sync_stop()
    return client, guarded_transport, guarded_sleep


def run_meta(job_name, prompt=None, *, max_job_seconds=900, poll_interval=15, max_requests=250,
             transport=None, key_provider=None, wall_time=time.time, monotonic=time.monotonic, sleep=time.sleep):
    """One fresh job or its owned saved state; never adopt/retry an uncertain POST."""
    if type(job_name) is not str or not JOB_RE.fullmatch(job_name):
        raise ContinuationError('invalid_job_name')
    if (type(max_job_seconds) is not int or not 30 <= max_job_seconds <= MAX_JOB_SECONDS
            or not _number(poll_interval) or not 0 < poll_interval <= 15
            or type(max_requests) is not int or not 2 <= max_requests <= 250):
        raise ContinuationError('invalid_limits')
    now, tick = wall_time(), monotonic()
    if not _number(now) or now < 0 or not _number(tick):
        raise ContinuationError('invalid_clock')
    _source_check()
    base = _local(CONT_ROOT)
    if base == ROOT.resolve():
        raise ContinuationError('continuation_directory_required')
    base.mkdir(exist_ok=True)
    for name in ('locks', 'bindings', 'jobs'):
        _local(base / name).mkdir(exist_ok=True)
    binding_path = _local(base / 'bindings' / (job_name + '.json'))
    output = _local(base / 'jobs' / job_name)
    lock = _local(base / 'locks' / (job_name + '.lock'))
    token = uuid.uuid4().hex
    _exclusive(lock, {'token': token, 'pid': os.getpid()})
    try:
        if binding_path.exists():
            binding = _binding(binding_path, job_name)
            if not (output / 'state.json').is_file():
                raise ContinuationError('orphan_initialization_no_retry')
            if prompt is not None and (type(prompt) is not str or hashlib.sha256(prompt.encode()).hexdigest() != binding['prompt_sha256']):
                raise ContinuationError('prompt_changed')
        else:
            if output.exists():
                raise ContinuationError('unbound_or_old_output_directory')
            if (base / 'STOP').exists():
                raise ContinuationError('continuation_stopped')
            if type(prompt) is not str or not prompt.strip() or len(prompt.encode('utf-8')) > 262144:
                raise ContinuationError('public_prompt_required')
            ExistingLedger()  # Check existing caps before key lookup or job creation.
            binding = {'version': 1, 'kind': 'bounded-meta-continuation', 'job_name': job_name,
                       'job_id': uuid.uuid4().hex, 'prompt_sha256': hashlib.sha256(prompt.encode()).hexdigest(),
                       'created_epoch': now, 'deadline_epoch': now + max_job_seconds,
                       'max_job_seconds': max_job_seconds, 'poll_interval': poll_interval,
                       'max_requests': max_requests, 'caps_usd': CAPS.copy(), 'client_sha256_lf': CLIENT_SHA256_LF}
            _exclusive(binding_path, binding)
        if now < binding['created_epoch'] - 1:
            raise ContinuationError('clock_regression')
        process_end = tick + max(0, binding['deadline_epoch'] - now)
        client, guarded_transport, guarded_sleep = _client(binding_path, binding, output,
            wall_time, monotonic, sleep, process_end, transport)
        return client.run_background(prompt, output_dir=output, max_job_seconds=binding['max_job_seconds'],
            poll_interval=binding['poll_interval'], max_requests=binding['max_requests'],
            transport=guarded_transport, key_provider=key_provider,
            wall_time=wall_time, monotonic=monotonic, sleep=guarded_sleep)
    finally:
        if _read(lock).get('token') == token:
            lock.unlink()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--job', required=True)
    parser.add_argument('--prompt-stdin', action='store_true')
    parser.add_argument('--max-job-seconds', type=int, default=900)
    args = parser.parse_args(argv)
    prompt = None
    if args.prompt_stdin:
        raw = sys.stdin.buffer.read(262145)
        if len(raw) > 262144:
            raise ContinuationError('public_prompt_too_large')
        prompt = raw.decode('utf-8')
    state = run_meta(args.job, prompt, max_job_seconds=args.max_job_seconds)
    print(json.dumps({key: state.get(key) for key in ('phase', 'finished', 'incomplete', 'usage_status', 'cost_usd', 'error_category')}, indent=2))
    return 0 if state['finished'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
