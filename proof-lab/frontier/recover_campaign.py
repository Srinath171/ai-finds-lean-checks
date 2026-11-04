"""Resume the authorized public-math investigation within the original limits."""
from pathlib import Path
from datetime import datetime, timezone
import json, time, math, sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from frontier import campaign as c

def main():
    deadline=datetime(2026,11,4,19,42,17,tzinfo=timezone.utc).timestamp()
    histories=[json.loads((ROOT/'frontier'/name/'status.json').read_text(encoding='utf-8')) for name in ('campaign-results','campaign-followup')]
    for state in histories:
        if state.get('phase')!='STOPPED' or state.get('status')!='NOT_SOLVED' or type(state.get('rounds_started')) is not int or not 0<=state['rounds_started']<=12:
            raise SystemExit('Previous state active or requires review; no request.')
        prior_deadline=state.get('deadline_epoch')
        if type(prior_deadline) not in (int,float) or not math.isfinite(prior_deadline):
            raise SystemExit('Invalid original deadline; no request.')
        deadline=min(deadline,prior_deadline)
    remaining=(deadline-time.time())/3600
    rounds=12-sum(state['rounds_started'] for state in histories)
    if not 0<remaining<=7 or not 1<=rounds<=12:
        raise SystemExit('Original time/combined-round allowance exhausted; no request.')
    c.SEED+=(ROOT/'frontier/recovery-seed.txt').read_text(encoding='utf-8')
    return c.run_campaign(output_dir=ROOT/'frontier/campaign-recovery',hours=remaining,max_rounds=rounds,request_timeout=600)

if __name__=='__main__':
    main()
