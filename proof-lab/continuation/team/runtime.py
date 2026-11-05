"""Fixed isolated native-Python entry point; no providers or environment files."""
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[2]
SITE = ROOT / '.venv' / 'Lib' / 'site-packages'
if not SITE.is_dir() or SITE.resolve() != SITE.absolute():
    raise RuntimeError('project_virtual_environment_required')
# -I -S keeps ambient/user-site/.pth injection out; add only the task's two roots.
sys.path.insert(0, str(SITE))
sys.path.insert(0, str(ROOT))
runpy.run_module('continuation.team.controller', run_name='__main__', alter_sys=True)
