"""Build the paper with latexmk and publish its PDF and bibliography."""
from pathlib import Path
import subprocess

def main():
    root = Path(__file__).resolve().parents[1]
    out = root / 'build' / 'paper'
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                    '-outdir=' + str(out), 'main.tex'], cwd=root / 'paper', check=True)
    log = (out / 'main.log').read_text(encoding='utf-8', errors='replace')
    for warning in ('Overfull \\hbox', 'There were undefined references', 'There were undefined citations'):
        if warning in log:
            raise RuntimeError('Inspect the TeX log: ' + warning)
    print('PASS rebuilt paper: ' + str(out / 'main.pdf'))

if __name__ == '__main__':
    main()
