import subprocess
import os
import sys

def test_mc_gdpr_consentwithdrawn():
    """End to end test - generate a Mermaid timeline for MC_GDPR_Consentwithdrawn.out"""
    inp = os.path.join(os.path.dirname(__file__), "..", "MC_GDPR_Consentwithdrawn.out")
    # Output target
    out = os.path.join(os.path.dirname(__file__), "test_timeline.mmd")
    ret = subprocess.run([
        sys.executable, os.path.join(os.path.dirname(__file__), "trace2mermaid.py"), inp, "-o", out
    ], capture_output=True)
    assert ret.returncode == 0
    with open(out) as f:
        txt = f.read()
    assert "gantt" in txt and "section" in txt
    print("Test succeeded! Mermaid output:")
    print(txt)

if __name__ == "__main__":
    test_mc_gdpr_consentwithdrawn()