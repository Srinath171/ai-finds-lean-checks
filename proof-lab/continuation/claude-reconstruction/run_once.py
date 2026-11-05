from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, time
from frontier.campaign import claude_critique
p=Path(__file__).resolve().parent
prompt=(p/'prompt.md').read_text(encoding='utf-8')
state={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),'pid':os.getpid(),'timeout_seconds':600,'model_alias':'opus','effort':'high','billing':'Claude Code subscription; API environment variables removed','prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest()}
with (p/'state.json').open('x',encoding='utf-8') as f: json.dump(state,f,indent=2)
started=time.monotonic()
try:
 result=claude_critique(prompt,timeout=600)
 (p/'visible-response.md').write_text(result['text']+'\n',encoding='utf-8')
 usage=result.get('usage')
 safe_usage={k:v for k,v in usage.items() if type(v) in (int,float)} if isinstance(usage,dict) else None
 state.update(status='COMPLETE_UNVERIFIED',usage=safe_usage,list_price_usd=result.get('list_price_usd'),billing=result['billing'],visible_sha256=hashlib.sha256(result['text'].encode()).hexdigest())
except Exception as exc:
 state.update(status='BLOCKED_OR_FAILED',error_type=type(exc).__name__)
finally:
 state.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=round(time.monotonic()-started,3))
 (p/'state.json').write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:state.get(k) for k in ['status','elapsed_seconds','list_price_usd','billing','error_type']}),flush=True)
