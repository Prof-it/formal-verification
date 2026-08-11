# trace2mermaid: GDPR TLA+ TLC Trace Visualizer

This tool parses TLC trace output from GDPR event-driven TLA+ models and creates a Mermaid Gantt diagram, showing events and period validity intervals over time, with readable, line-broken timestamps.

## Usage

1. Activate your environment:
   ```
   source venv/bin/activate
   ```

2. Run on a TLC model checker .out trace:
   ```
   python trace2mermaid.py path/to/MC_GDPR_Consentwithdrawn.out  > timeline.mmd
   # or use -o timeline.mmd
   ```

3. Paste the generated `timeline.mmd` into https://mermaid.live **for visualization**.

## Features
- Automatically parses DPV/GDPR fields (Consent/Contract/Processing periods).
- Shows periods and events for each DataSubject.
- Timestamps formatted with year on line 1, mm-dd HH:MM on line 2 (labels).
- Can highlight compliance violations if trace indicates.

## Requirements
- Python 3.8+
- [typer](https://github.com/tiangolo/typer)
- [openai](https://github.com/openai/openai-python)
- [python-dotenv](https://github.com/theskumar/python-dotenv)
- [beautifulsoup4](https://www.crummy.com/software/BeautifulSoup/)
- [lxml](https://lxml.de/)
- [pytest](https://docs.pytest.org/en/stable/)

All dependencies are listed in [`requirements.txt`](requirements.txt). Install them with:
```
pip install -r requirements.txt
```

## Test
Run all tests with:
```
pytest
```
Or run the main test script directly:
```
python test_trace2mermaid.py
```

---
See `test_trace2mermaid.py` for example usage/test cases on GDPR sample outputs.
