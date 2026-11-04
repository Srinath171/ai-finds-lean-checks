"""A new targeted audit batch; money caps and original deadline never reset."""
from pathlib import Path
from datetime import datetime, timezone
import json,time,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from frontier import campaign as c

def main():
    for name in ('campaign-results','campaign-followup','campaign-recovery'):
        state=json.loads((ROOT/'frontier'/name/'status.json').read_text(encoding='utf-8'))
        if state.get('phase')!='STOPPED' or state.get('status')!='NOT_SOLVED':
            raise SystemExit('Earlier batch active or needs review; no request.')
    remaining=(datetime(2026,11,4,19,42,17,tzinfo=timezone.utc).timestamp()-time.time())/3600
    if not 0<remaining<=7:
        raise SystemExit('Original deadline passed; no request.')
    c.SEED+=(ROOT/'frontier/sparse-audit-seed.txt').read_text(encoding='utf-8')
    return c.run_campaign(output_dir=ROOT/'frontier/campaign-sparse-audit',hours=remaining,max_rounds=3,request_timeout=600)

if __name__=='__main__':
    main()
