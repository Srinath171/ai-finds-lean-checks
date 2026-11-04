"""Isolated second-phase Meta guard. No paid requests occur during import/init.

Uses a private module instance of the frozen background client. The original
module, deadline, and job folders are never modified or resumed by this adapter.
"""
from __future__ import annotations
import argparse
from datetime import datetime
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
from budget import BudgetLedger,BudgetError

ROOT=Path(__file__).resolve().parents[1]
PHASE_ROOT=ROOT/'hour2'
LEDGER_PATH=ROOT/'logs'/'spending.json'
CLIENT_SOURCE=ROOT/'frontier'/'background_meta.py'
CLIENT_SHA256_LF='730551c9ff0f2215e207df0cfb599506e86863bfcfa88b18f76c78eddd4fcaed'
PHASE_ID='hour2-20261104T194830Z'
START_UTC='2026-11-04T19:48:30+00:00'
DEADLINE_UTC='2026-11-04T20:48:30+00:00'
START=datetime.fromisoformat(START_UTC).timestamp()
DEADLINE=datetime.fromisoformat(DEADLINE_UTC).timestamp()
NETWORK_CUTOFF=DEADLINE-15
CAPS={'meta':'115','claude':'40'}
JOB_RE=re.compile(r'[a-z0-9][a-z0-9_-]{0,63}\Z')


class PhaseError(RuntimeError): pass


def _window(wall):
    now=wall()
    if type(now) not in (int,float) or not math.isfinite(now) or not START<=now<NETWORK_CUTOFF:
        raise PhaseError('outside_immutable_phase_window')
    return now


def _source_check():
    raw=CLIENT_SOURCE.read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
    if hashlib.sha256(raw).hexdigest()!=CLIENT_SHA256_LF:
        raise PhaseError('frozen_background_client_changed')


def _config():
    return {'version':1,'phase_id':PHASE_ID,'start_utc':START_UTC,'deadline_utc':DEADLINE_UTC,
            'last_network_epoch':NETWORK_CUTOFF,'max_job_seconds':1800,
            'caps_usd':CAPS,'ledger_path':str(LEDGER_PATH.resolve()),
            'client_sha256_lf':CLIENT_SHA256_LF,'no_old_jobs_or_response_ids':True}


def _read_json(path):
    def pairs(items):
        data={}
        for key,value in items:
            if key in data: raise PhaseError('duplicate_json_key')
            data[key]=value
        return data
    raw=path.read_bytes()
    if len(raw)>2*1024*1024: raise PhaseError('metadata_too_large')
    try:
        return json.loads(raw.decode('utf-8'),object_pairs_hook=pairs,
                          parse_constant=lambda value:(_ for _ in ()).throw(PhaseError('nonfinite_json')))
    except (ValueError,UnicodeError): raise PhaseError('invalid_metadata') from None


def _exclusive_json(path,data):
    with path.open('x',encoding='utf-8') as handle:
        json.dump(data,handle,sort_keys=True,allow_nan=False,indent=2)
        handle.write('\n');handle.flush();os.fsync(handle.fileno())


def _phase_config():
    _source_check()
    actual=_read_json(PHASE_ROOT/'phase_budget.json')
    expected=_config()
    if type(actual) is not dict or type(actual.get('version')) is not int or actual!=expected:
        raise PhaseError('immutable_phase_config_mismatch')
    return actual


class PhaseLedger(BudgetLedger):
    """Existing shared ledger only; both provider caps checked under every lock."""
    def __init__(self,path=None,*,wall_time=time.time):
        self.path=Path(LEDGER_PATH if path is None else path).resolve()
        self.lock_path=self.path.with_name(self.path.name+'.lock')
        self.lock_timeout=2.0
        self.wall_time=wall_time
        self.status()  # No create/reset path.
    def _read(self):
        state=super()._read()
        if any(Decimal(state['caps_usd'][p])>Decimal(CAPS[p]) for p in CAPS):
            raise BudgetError('shared_provider_cap_exceeds_phase_authorization')
        return state
    def reserve(self,provider,upper_bound_usd,*,purpose=''):
        _window(self.wall_time)
        return super().reserve(provider,upper_bound_usd,purpose=purpose)


def initialize_phase(*,wall_time=time.time):
    """Create immutable config once; never change ledger balances or caps here."""
    _window(wall_time);_source_check()
    ledger=PhaseLedger(wall_time=wall_time)
    PHASE_ROOT.mkdir(parents=True,exist_ok=True)
    config_path=PHASE_ROOT/'phase_budget.json'
    try: _exclusive_json(config_path,_config())
    except FileExistsError: pass
    _phase_config()
    return {'phase_id':PHASE_ID,'deadline_utc':DEADLINE_UTC,
            'providers':ledger.status()['providers']}


def _binding(path,job):
    data=_read_json(path)
    expected={'phase_id','job_name','output_relative','created_epoch','job_id'}
    if (type(data) is not dict or set(data)!=expected or data['phase_id']!=PHASE_ID
            or data['job_name']!=job or data['output_relative']!='jobs/'+job
            or type(data['created_epoch']) not in (int,float) or not math.isfinite(data['created_epoch'])
            or not START<=data['created_epoch']<NETWORK_CUTOFF
            or (data['job_id'] is not None and (type(data['job_id']) is not str or not re.fullmatch(r'[0-9a-f]{32}',data['job_id'])))):
        raise PhaseError('invalid_phase_job_binding')
    return data


def _bound_state(state,binding):
    if type(state) is not dict: raise PhaseError('invalid_phase_state')
    for name in ('started_epoch','deadline_epoch','max_job_seconds'):
        if type(state.get(name)) not in (int,float) or not math.isfinite(state[name]):
            raise PhaseError('invalid_phase_state_time')
    if (not START<=state['started_epoch']<NETWORK_CUTOFF or not 0<state['max_job_seconds']<=1800
            or not state['started_epoch']<state['deadline_epoch']<=min(NETWORK_CUTOFF,state['started_epoch']+state['max_job_seconds'])
            or binding['job_id']!=state.get('job_id')):
        raise PhaseError('old_or_unbound_phase_state')


def _client(binding_path,job,wall,mono):
    """Execute frozen local source in private globals, never change old globals."""
    _source_check()
    spec=importlib.util.spec_from_file_location('_hour2_private_background_meta',CLIENT_SOURCE)
    client=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(client)
    client.HARD_DEADLINE=NETWORK_CUTOFF
    client.HARD_DEADLINE_UTC=datetime.fromtimestamp(NETWORK_CUTOFF,datetime.fromisoformat(DEADLINE_UTC).tzinfo).isoformat()
    client.LEDGER_PATH=LEDGER_PATH
    class GuardedLedger(PhaseLedger):
        def __init__(self,path):super().__init__(path,wall_time=wall)
    client.ExistingMetaLedger=GuardedLedger
    base=client._Session
    class GuardedSession(base):
        def save(self):
            binding=_binding(binding_path,job)
            if binding['job_id'] is None:
                if (self.state.get('phase')!='PREPARING' or self.state.get('response_id') is not None
                        or self.state.get('request_count')!=0 or (self.output/'state.json').exists()):
                    raise PhaseError('cannot_adopt_existing_state')
                binding['job_id']=self.state['job_id']
                _bound_state(self.state,binding)
                client._save(binding_path,binding)
            else:_bound_state(self.state,binding)
            return super().save()
        def request(self,kind,payload=None):
            _phase_config()
            _window(wall)
            with self.ledger._locked():self.ledger._read()
            return super().request(kind,payload)
    client._Session=GuardedSession
    original_validate=client._validate_state
    def validate(state,ledger,output):
        _bound_state(state,_binding(binding_path,job))
        return original_validate(state,ledger,output)
    client._validate_state=validate
    return client


def run_meta(job_name,prompt=None,*,max_job_seconds=1800,poll_interval=15,max_requests=250,
             transport=None,key_provider=None,wall_time=time.time,monotonic=time.monotonic,sleep=time.sleep):
    """Only new phase-owned job names; accepted/uncertain jobs are never resubmitted."""
    if type(job_name) is not str or not JOB_RE.fullmatch(job_name):raise PhaseError('invalid_phase_job_name')
    if type(max_job_seconds) not in (int,float) or not math.isfinite(max_job_seconds) or not 0<max_job_seconds<=1800:
        raise PhaseError('invalid_phase_job_duration')
    now=_window(wall_time);_phase_config()
    phase_mono_end=monotonic()+NETWORK_CUTOFF-now
    phase=PHASE_ROOT.resolve()
    if not phase.is_relative_to(ROOT) or phase==ROOT:raise PhaseError('phase_outside_project')
    locks=phase/'locks';bindings=phase/'bindings';jobs=phase/'jobs'
    for directory in (locks,bindings,jobs):directory.mkdir(exist_ok=True)
    output=jobs/job_name
    binding_path=bindings/(job_name+'.json')
    lock=locks/(job_name+'.lock')
    fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600);os.close(fd)
    try:
        if binding_path.exists():
            binding=_binding(binding_path,job_name)
            if binding['job_id'] is None or not (output/'state.json').is_file():
                raise PhaseError('prior_initialization_outcome_uncertain')
            _bound_state(_read_json(output/'state.json'),binding)
        else:
            if output.exists():raise PhaseError('refuse_unbound_or_old_output_directory')
            if type(prompt) is not str or not prompt.strip():raise PhaseError('new_job_requires_public_prompt')
            _exclusive_json(binding_path,{'phase_id':PHASE_ID,'job_name':job_name,
                'output_relative':'jobs/'+job_name,'created_epoch':now,'job_id':None})
        client=_client(binding_path,job_name,wall_time,monotonic)
        actual_transport=transport or client.http_transport
        def guarded_transport(method,url,payload,timeout,key):
            _phase_config();_window(wall_time)
            remaining=min(NETWORK_CUTOFF-wall_time(),phase_mono_end-monotonic())
            if remaining<=0:raise client.SafeError('deadline')
            ledger=PhaseLedger(wall_time=wall_time)
            with ledger._locked():ledger._read()
            return actual_transport(method,url,payload,min(timeout,remaining),key)
        return client.run_background(prompt,output_dir=output,max_job_seconds=max_job_seconds,
            poll_interval=poll_interval,max_requests=max_requests,transport=guarded_transport,
            key_provider=key_provider,wall_time=wall_time,monotonic=monotonic,sleep=sleep)
    finally:lock.unlink()


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--init',action='store_true')
    parser.add_argument('--job')
    parser.add_argument('--prompt-stdin',action='store_true')
    parser.add_argument('--max-job-seconds',type=float,default=1800)
    args=parser.parse_args(argv)
    if args.init:
        print(json.dumps(initialize_phase(),indent=2));return 0
    if not args.job:parser.error('--job is required')
    prompt=None
    if args.prompt_stdin:
        raw=sys.stdin.buffer.read(262145)
        if len(raw)>262144:raise PhaseError('public_prompt_too_large')
        prompt=raw.decode('utf-8')
    state=run_meta(args.job,prompt,max_job_seconds=args.max_job_seconds)
    print(json.dumps({key:state.get(key) for key in ('phase','finished','incomplete','usage_status','cost_usd','error_category')},indent=2))
    return 0 if state['finished'] else 1


if __name__=='__main__':raise SystemExit(main())
