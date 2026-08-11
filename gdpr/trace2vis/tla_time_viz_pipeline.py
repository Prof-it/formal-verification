import subprocess
import sys
from pathlib import Path
import os

def run_tlc_and_continue_on_violation(tla_path, cfg_path, out_file, tla2tools_jar):
    import subprocess
    model_dir = os.path.dirname(tla_path)
    tla_name = os.path.basename(tla_path)
    cfg_name = os.path.basename(cfg_path)
    cwd = os.getcwd()
    try:
        os.chdir(model_dir)
        cmd = [
            "java", "-cp", tla2tools_jar,
            "tlc2.TLC",
            tla_name,
            "-config", cfg_name,
        ]
        print(f"$ {' '.join(cmd)} > {out_file}")
        with open(out_file, "w") as f:
            result = subprocess.run(cmd, stdout=f, stderr=subprocess.PIPE)
        if not os.path.isfile(out_file):
            raise RuntimeError("TLC failed to produce output file")
    finally:
        os.chdir(cwd)


def run(cmd, check=True, capture_output=None):
    print(f"$ {' '.join(str(c) for c in cmd)}")
    if capture_output is not None:
        result = subprocess.run(cmd, check=check, stdout=capture_output)
    else:
        result = subprocess.run(cmd, check=check)
    if result.returncode != 0:
        print(f"Error running: {' '.join(str(c) for c in cmd)}")
        sys.exit(1)

def run_pipeline_for_pair(tla_path, cfg_path, crop_amount=50):
    tla_path = Path(tla_path).resolve()
    cfg_path = Path(cfg_path).resolve()
    CFGBASE = cfg_path.with_suffix('').name
    REPORT_DIR = cfg_path.parent / "report"
    REPORT_DIR.mkdir(exist_ok=True)

    OUT = REPORT_DIR / f"{CFGBASE}.out"
    MMD = REPORT_DIR / f"{CFGBASE}.mmd"
    RAWSVG = REPORT_DIR / f"{CFGBASE}.raw.svg"
    CROP_SVG = REPORT_DIR / f"{CFGBASE}.cropped.svg"
    PNG = REPORT_DIR / f"{CFGBASE}.png"
    TLA2TOOLS_JAR = str((tla_path.parent / "../tla_modules/tla2tools.jar").resolve())


    # 1. TLC (in gdpr dir, with correct CLI)
    TLA2TOOLS_JAR = str((tla_path.parent / "../tla_modules/tla2tools.jar").resolve())
    print("Running TLC...")
    run_tlc_and_continue_on_violation(str(tla_path), str(cfg_path), str(OUT), TLA2TOOLS_JAR)


    # 2. Mermaid .mmd from .out via LLM
    print("Generating Mermaid diagram via LLM...")
    run([
        sys.executable, "trace2mermaid_llm.py",
        str(OUT),
        "-o", str(MMD)
    ])

    # 3. .mmd → SVG via mmdc
    print("Rendering raw SVG...")
    run([
        "mmdc",
        "-i", str(MMD),
        "-o", str(RAWSVG)
    ])

    # 4. Crop SVG
    print(f"Cropping bottom {crop_amount} units from SVG...")
    run([
        sys.executable, "crop_svg_bottom.py",
        str(RAWSVG),
        str(CROP_SVG),
        str(crop_amount)
    ])

    # 5. SVG to PNG (inkscape or other converter)
    print("Exporting to PNG...")
    run([
        '/Applications/Inkscape.app/Contents/MacOS/inkscape',
        str(CROP_SVG),
        "--export-type=png",
        "--export-filename=" + str(PNG)
    ])

    print(f"Pipeline complete! Outputs:\n{OUT}\n{MMD}\n{RAWSVG}\n{CROP_SVG}\n{PNG}")

def main():
    import glob
    BASEDIR = Path(__file__).parent.parent.resolve()   # This resolves to gdpr/
    TLA_PATH = BASEDIR / "MC_GDPR_Time.tla"
    CFG_FILES = list(sorted(BASEDIR.glob("*.cfg")))
    if not TLA_PATH.exists():
        print(f"Model file {TLA_PATH} not found!")
        sys.exit(1)
    if not CFG_FILES:
        print("No .cfg files found in working directory!")
        sys.exit(1)
    for cfg in CFG_FILES:
        print("="*40)
        print(f"Processing: {cfg.name} with {TLA_PATH.name}")
        try:
            run_pipeline_for_pair(str(TLA_PATH), str(cfg), crop_amount=50)
            print(f"Completed {cfg.name}")
        except Exception as e:
            print(f"{cfg.name}: Skipped or failed. ({e})")



if __name__ == "__main__":
    main()
