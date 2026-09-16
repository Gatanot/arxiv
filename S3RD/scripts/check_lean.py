"""Fresh rebuild, kernel-axiom audit, source hashes; no search or generated proof assumptions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

MODULES=['Core','Assembly','Blocks','LowerBound','UpperBounds','OddCircumference','Semantics','Main',
         'ColorCycle','ColorPeriod','WidthThree','WidthThreePeriod','Classification','WidthThreeCount',
         'EqualitySupport','EvenWidths','WidthFourSearch','WidthFour','Audit']


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--lean', default='lean', help='Lean 4.33.0 executable (default: lean on PATH)')
    p.add_argument('--timeout',type=float,default=1200)
    args=p.parse_args()
    compiler=shutil.which(args.lean)
    if compiler is None:
        p.error('Lean not found. Supply --lean /absolute/path/to/lean (Lean 4.33.0).')
    root=Path(__file__).resolve().parents[1]
    repo=root
    build=root/'build'
    output_dir=build/'S3RD'/'lean'
    output_dir.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_PATH=str(build),PYTHONUTF8='1')
    version=subprocess.run([compiler,'--version'],capture_output=True,text=True,check=True,timeout=10).stdout.strip()
    if not re.search(r'version 4\.33\.0(?:,|\s|\))', version):
        p.error(f'Expected Lean 4.33.0; found {version}')
    report={'status':'RUNNING','lean_version':version,
            'scope':'For every m>=5 and every n>=3: the exact singleton 3-rainbow domination number is (m*n+1)/2 plus n mod 2 when m is even, and with no correction when m is odd. Width four is exact for every odd n, n=4, n=6, every even n>=10, and n=8 with value 18. The width-three exception classification is also included. Natural-number division is used.',
            'excluded':'Publication priority and literature comparison are not formalized. The formal development does not by itself establish an originality claim.',
            'checks':[]}
    path=root/'build'/'reports'/'lean_report.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
    try:
        for name in MODULES:
            source=root/'S3RD'/'lean'/f'{name}.lean'
            data=source.read_bytes()
            text=data.decode('utf-8')
            if re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b', re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)):
                raise RuntimeError(f'Forbidden proof escape in {name}')
            start=time.monotonic()
            proc=subprocess.run([compiler,'-o',str(output_dir/f'{name}.olean'),str(source)],
                                cwd=repo,env=env,capture_output=True,text=True,encoding='utf-8',timeout=args.timeout)
            log=proc.stdout+proc.stderr
            if proc.returncode or 'sorryAx' in log:
                raise RuntimeError(f'{name}:\n{log}')
            axiom_sets=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
            if not axiom_sets:raise RuntimeError(f'Missing axiom audit in {name}')
            for item in axiom_sets:
                unknown={x.strip() for x in item.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}
                if unknown:raise RuntimeError(f'Unexpected axioms in {name}: {unknown}')
            report['checks'].append({'module':name,'sha256':hashlib.sha256(data).hexdigest(),
                                     'seconds':round(time.monotonic()-start,3),'output':log})
            print(f'PASS {name}',flush=True)
        report['status']='PASS'
    except Exception as exc:
        report['status']='FAIL'
        report['error']=str(exc)
        raise
    finally:
        path.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(report['scope'])


if __name__=='__main__':main()
