"""One bounded public-math audit; no automatic new Meta request."""
from pathlib import Path
from datetime import datetime,timezone
import json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from frontier.background_meta import run_background

def main():
    output=ROOT/'frontier/background-meta/optimal-support'
    prompt=(ROOT/'frontier/optimal-support-prompt.txt').read_text(encoding='utf-8')
    state=run_background(prompt,output_dir=output,max_job_seconds=2700)
    remaining=datetime(2026,11,4,19,42,17,tzinfo=timezone.utc).timestamp()-time.time()
    if not state['incomplete'] and state.get('visible_text') and remaining>1 and not (output/'claude-audit.json').exists():
        from frontier.campaign import claude_critique
        text='Public mathematics only. Independently audit this UNVERIFIED model answer about parity-phase support and MCSP. Find a gap/counterexample. No source/files/tools/accounts. Do not mark PvsNP solved.\n'+state['visible_text']
        try:
            result=claude_critique(text,timeout=min(240,remaining))
        except Exception as exc:
            result={'status':'critique_failed','error_type':type(exc).__name__}
        (output/'claude-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    summary={k:state.get(k) for k in ('phase','remote_status','finished','incomplete','usage_status','cost_usd','error_category','cancellation_confirmed')}
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary),flush=True)

if __name__=='__main__':
    main()
