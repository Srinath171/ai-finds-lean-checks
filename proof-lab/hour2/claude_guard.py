"""One-shot, deadline-bound Fable MAX worker for explicitly supplied public math.

No source attachments, model tools, retry, key reads, or network calls on import.
A saved job is never submitted again, including after timeout or process failure.
"""
from __future__ import annotations
import argparse
from decimal import Decimal
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import threading
import time
from hour2 import phase_guard as phase

MAX_PROMPT=262144
MAX_VISIBLE=1048576
MAX_CAPTURE=2097152
ERRORS={'configuration_error','invalid_request','budget_error','http_error','invalid_response','transport_error','phase_guard','worker_error'}


def _save(path,data):
    temp=path.with_name(path.name+'.tmp')
    with temp.open('w',encoding='utf-8') as handle:
        json.dump(data,handle,ensure_ascii=False,allow_nan=False,indent=2)
        handle.write('\n');handle.flush();os.fsync(handle.fileno())
    os.replace(temp,path)


def _finite(value):return type(value) in (int,float) and math.isfinite(value)


def _worker(payload,*,wall=time.time,mono=time.monotonic):
    """Fixed operation; called only by an explicitly launched authorized worker."""
    import research_client as client
    try:
        phase._phase_config();phase._window(wall)
        required={'phase_id','prompt','started_epoch','deadline_epoch','max_tokens'}
        if type(payload) is not dict or set(payload)!=required or payload['phase_id']!=phase.PHASE_ID:
            raise phase.PhaseError('invalid_worker_payload')
        prompt,start,end,tokens=(payload[k] for k in ('prompt','started_epoch','deadline_epoch','max_tokens'))
        if (type(prompt) is not str or not prompt.strip() or len(prompt.encode('utf-8'))>MAX_PROMPT
                or not _finite(start) or not _finite(end) or not phase.START<=start<=wall()
                or not start<end<=min(phase.NETWORK_CUTOFF,start+1800)
                or type(tokens) is not int or not 1<=tokens<=65536):
            raise phase.PhaseError('invalid_worker_limits')
        mono_end=mono()+end-wall()
        original_open=client._open_request
        original_key=client._read_api_key
        original_ledger=client._ledger
        loaded_key=[]
        def key():
            phase._phase_config();phase._window(wall)
            value=original_key();loaded_key.append(value);return value
        def ledger():return phase.PhaseLedger(wall_time=wall)
        def guarded_open(request,*,timeout):
            phase._phase_config();phase._window(wall)
            remaining=min(end-wall(),mono_end-mono())
            if remaining<=0:raise phase.PhaseError('worker_deadline')
            current=ledger()
            with current._locked():current._read()
            return original_open(request,timeout=min(timeout,remaining))
        client._read_api_key=key;client._ledger=ledger;client._open_request=guarded_open
        try:
            remaining=min(end-wall(),mono_end-mono())
            if remaining<=0:raise phase.PhaseError('worker_deadline')
            result=client.ask_public_math(prompt,max_tokens=tokens,timeout=min(1800,remaining))
        finally:
            client._read_api_key=original_key;client._open_request=original_open
            # The worker process exits; restore the original module ledger too.
            client._ledger=original_ledger
        visible=result['text']
        for secret in loaded_key:visible=visible.replace(secret,'[REDACTED]')
        if len(visible.encode('utf-8'))>MAX_VISIBLE:raise phase.PhaseError('visible_output_limit')
        return {'ok':True,'text':visible,'incomplete':result['incomplete'],
                'stop_reason':result['stop_reason'] if result['stop_reason'] in ('end_turn','max_tokens','stop_sequence','tool_use','pause_turn','refusal') else 'other',
                'usage':result['usage'],'usage_status':result['usage_status'],
                'cost_usd':result['cost_usd'],'reserved_usd':result['reserved_usd'],
                'model':client.MODEL,'claim_status':'UNVERIFIED'}
    except client.ResearchError as exc:
        return {'ok':False,'error_category':exc.status if exc.status in ERRORS else 'worker_error',
                'http_status':exc.http_status if type(exc.http_status) is int and 100<=exc.http_status<=599 else None}
    except phase.PhaseError:
        return {'ok':False,'error_category':'phase_guard','http_status':None}
    except Exception:
        return {'ok':False,'error_category':'worker_error','http_status':None}


def _capture(payload,timeout):
    """Bounded pipes and total monotonic timeout; unknown outcomes never retried."""
    end=time.monotonic()+timeout
    process=subprocess.Popen([sys.executable,'-B','-m','hour2.claude_guard','--worker'],
        cwd=phase.ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
        shell=False,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
    buffer=bytearray();overflow=threading.Event();count=[0];guard=threading.Lock()
    def read(stream,keep):
        try:
            while True:
                chunk=stream.read(8192)
                if not chunk:break
                with guard:
                    count[0]+=len(chunk)
                    if count[0]>MAX_CAPTURE:overflow.set();break
                    if keep:buffer.extend(chunk)
        except (OSError,ValueError):pass
    def write():
        try:
            process.stdin.write(json.dumps(payload,ensure_ascii=False).encode('utf-8'))
            process.stdin.close()
        except (OSError,ValueError):pass
    threads=[threading.Thread(target=read,args=(process.stdout,True),daemon=True),
             threading.Thread(target=read,args=(process.stderr,False),daemon=True),
             threading.Thread(target=write,daemon=True)]
    for thread in threads:thread.start()
    kind='completed'
    try:
        while process.poll() is None:
            if overflow.is_set():kind='output_limit';break
            if time.monotonic()>=end:kind='timeout';break
            time.sleep(min(.05,max(0,end-time.monotonic())))
        if kind!='completed':process.kill()
        process.wait(timeout=2)
        for thread in threads[:2]:thread.join(timeout=min(.1,max(0,end-time.monotonic())))
        if overflow.is_set():kind='output_limit'
        elif kind=='completed' and process.returncode!=0:kind='failed'
        return {'kind':kind,'stdout':bytes(buffer) if kind=='completed' else b''}
    finally:
        if process.poll() is None:process.kill()
        for stream in (process.stdin,process.stdout,process.stderr):
            try:stream.close()
            except (OSError,ValueError):pass


def _result(raw):
    def pairs(items):
        data={}
        for key,value in items:
            if key in data:raise ValueError('duplicate')
            data[key]=value
        return data
    result=json.loads(raw.decode('utf-8'),object_pairs_hook=pairs,
                      parse_constant=lambda value:(_ for _ in ()).throw(ValueError('nonfinite')))
    if type(result) is not dict or type(result.get('ok')) is not bool:raise ValueError('shape')
    if not result['ok']:
        if set(result)!={'ok','error_category','http_status'} or result['error_category'] not in ERRORS:
            raise ValueError('error_shape')
        code=result['http_status']
        if code is not None and (type(code) is not int or not 100<=code<=599):raise ValueError('http')
        return result
    fields={'ok','text','incomplete','stop_reason','usage','usage_status','cost_usd','reserved_usd','model','claim_status'}
    if (set(result)!=fields or result['model']!='claude-fable-5' or result['claim_status']!='UNVERIFIED'
            or type(result['text']) is not str or len(result['text'].encode('utf-8'))>MAX_VISIBLE
            or type(result['incomplete']) is not bool or result['usage_status'] not in ('settled','pending')
            or result['stop_reason'] not in ('end_turn','max_tokens','stop_sequence','tool_use','pause_turn','refusal','other')):
        raise ValueError('result_shape')
    for field in ('cost_usd','reserved_usd'):
        amount=result[field]
        if amount is None and field=='cost_usd':continue
        if type(amount) is not str or len(amount)>64 or not Decimal(amount).is_finite() or Decimal(amount)<0:
            raise ValueError('cost')
    usage=result['usage']
    allowed={'input_tokens','output_tokens','cache_read_input_tokens','cache_creation_input_tokens',
             'ephemeral_5m_input_tokens','ephemeral_1h_input_tokens'}
    if usage is not None and (type(usage) is not dict or set(usage)!=allowed
            or any(type(value) is not int or value<0 for value in usage.values())):
        raise ValueError('usage')
    if result['usage_status']=='settled' and (usage is None or result['cost_usd'] is None):raise ValueError('settlement')
    return result


def run_claude(job_name,prompt=None,*,max_job_seconds=1800,max_tokens=65536,
               process_runner=None,wall_time=time.time,monotonic=time.monotonic):
    if type(job_name) is not str or not phase.JOB_RE.fullmatch(job_name):raise phase.PhaseError('invalid_claude_job_name')
    if not _finite(max_job_seconds) or not 0<max_job_seconds<=1800:raise phase.PhaseError('invalid_claude_job_duration')
    if type(max_tokens) is not int or not 1<=max_tokens<=65536:raise phase.PhaseError('invalid_claude_tokens')
    now=phase._window(wall_time);phase._phase_config()
    phase.PhaseLedger(wall_time=wall_time)
    root=phase.PHASE_ROOT.resolve()
    if not root.is_relative_to(phase.ROOT) or root==phase.ROOT:raise phase.PhaseError('phase_outside_project')
    jobs=root/'claude-jobs';locks=root/'claude-locks'
    jobs.mkdir(exist_ok=True);locks.mkdir(exist_ok=True)
    output=(jobs/job_name).resolve()
    if not output.is_relative_to(root):raise phase.PhaseError('output_outside_phase')
    lock=locks/(job_name+'.lock')
    fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600);os.close(fd)
    try:
        state_path=output/'state.json'
        if output.exists():
            state=phase._read_json(state_path)
            if (type(state) is not dict or type(state.get('version')) is not int or state['version']!=1
                    or state.get('phase_id')!=phase.PHASE_ID or state.get('job_name')!=job_name
                    or state.get('status') not in ('STARTING','COMPLETED','UNCERTAIN')
                    or not _finite(state.get('started_epoch')) or not _finite(state.get('deadline_epoch'))
                    or not phase.START<=state['started_epoch']<state['deadline_epoch']<=min(phase.NETWORK_CUTOFF,state['started_epoch']+1800)):
                raise phase.PhaseError('old_or_invalid_claude_state')
            if prompt is not None and (type(prompt) is not str or hashlib.sha256(prompt.encode()).hexdigest()!=state.get('prompt_sha256')):
                raise phase.PhaseError('prompt_changed')
            if state['status']=='STARTING':
                state.update(status='UNCERTAIN',error_category='prior_worker_outcome_unknown');_save(state_path,state)
            return state  # Never submit any saved job again.
        if type(prompt) is not str or not prompt.strip() or len(prompt.encode('utf-8'))>MAX_PROMPT:
            raise phase.PhaseError('invalid_public_prompt')
        end=min(phase.NETWORK_CUTOFF,now+max_job_seconds)
        if end-now<=1:raise phase.PhaseError('insufficient_phase_time')
        output.mkdir()
        state={'version':1,'phase_id':phase.PHASE_ID,'job_name':job_name,'status':'STARTING',
               'started_epoch':now,'deadline_epoch':end,'prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest(),
               'claim_status':'UNVERIFIED','error_category':None}
        _save(state_path,state)
        mono_end=monotonic()+end-wall_time()
        phase._window(wall_time);phase._phase_config()
        timeout=min(end-wall_time(),mono_end-monotonic())
        if timeout<=0:
            state.update(status='UNCERTAIN',error_category='deadline_before_worker');_save(state_path,state);return state
        payload={'phase_id':phase.PHASE_ID,'prompt':prompt,'started_epoch':now,'deadline_epoch':end,'max_tokens':max_tokens}
        try:
            captured=(process_runner or _capture)(payload,timeout)
            if captured['kind']!='completed':
                state.update(status='UNCERTAIN',error_category=captured['kind'] if captured['kind'] in ('timeout','output_limit','failed') else 'worker_failure')
            else:
                result=_result(captured['stdout'])
                state.update(status='COMPLETED' if result['ok'] else 'UNCERTAIN',result=result,
                             error_category=None if result['ok'] else result['error_category'])
        except Exception:
            state.update(status='UNCERTAIN',error_category='worker_failure')
        _save(state_path,state);return state
    finally:lock.unlink()


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker',action='store_true');parser.add_argument('--job')
    parser.add_argument('--prompt-stdin',action='store_true');parser.add_argument('--max-job-seconds',type=float,default=1800)
    args=parser.parse_args(argv)
    raw=sys.stdin.buffer.read(MAX_PROMPT+8193) if args.worker or args.prompt_stdin else b''
    if args.worker:
        if len(raw)>MAX_PROMPT+8192:return 2
        result=_worker(json.loads(raw.decode('utf-8')))
        print(json.dumps(result,ensure_ascii=False),flush=True);return 0
    if not args.job:parser.error('--job is required')
    prompt=raw.decode('utf-8') if args.prompt_stdin else None
    state=run_claude(args.job,prompt,max_job_seconds=args.max_job_seconds)
    print(json.dumps({'status':state['status'],'error_category':state.get('error_category')}));return 0 if state['status']=='COMPLETED' else 1


if __name__=='__main__':raise SystemExit(main())
