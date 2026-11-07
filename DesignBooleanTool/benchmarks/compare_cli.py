"""User-facing CLI wall time including fresh process, JSON parsing and JSON output."""
import argparse,json,statistics,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'examples'))
from generate import make_fixture

def main():
    p=argparse.ArgumentParser();p.add_argument('--old-python',type=Path,required=True);p.add_argument('--new-python',type=Path,required=True);p.add_argument('--repeats',type=int,default=5);p.add_argument('--output',type=Path,default=Path(__file__).with_name('cli-results.json'));a=p.parse_args()
    records=[]
    with tempfile.TemporaryDirectory(prefix='design-boolean-cli-') as folder:
        path=Path(folder)/'input.json'
        for family,m in [('plateaued-stabilization',5),('quadratic-family',8),('quadratic-family',10)]:
            data=make_fixture(family,m);path.write_text(json.dumps({'incidence':data['incidence']},separators=(',',':')),encoding='utf-8')
            methods={}
            for name,python in [('python_v0_1',a.old_python),('native_v0_2',a.new_python)]:
                samples=[]
                for index in range(a.repeats+1):
                    start=time.perf_counter_ns();process=subprocess.run([str(python),'-I','-m','design_boolean','recognize',str(path)],cwd=folder,capture_output=True,text=True,timeout=120)
                    duration=(time.perf_counter_ns()-start)/1e6
                    if process.returncode:raise RuntimeError(process.stderr)
                    answer=json.loads(process.stdout);assert answer['status']=='recognized'
                    if name=='native_v0_2':assert answer['diagnostics']['backend']=='native'
                    if index:samples.append(duration)
                methods[name]={'median_ms':statistics.median(samples),'samples_ms':samples}
            records.append({'id':data['id'],'points':len(data['incidence']),'blocks':len(data['incidence'][0]),'measurements':methods})
            print(data['id'],{k:round(v['median_ms'],3) for k,v in methods.items()},flush=True)
    a.output.write_text(json.dumps({'scope':'Fresh CLI process from unrelated folder; same JSON input; all parsing, recognition, certificate construction and stdout JSON included; parent parsing excluded','repeats':a.repeats,'warmups':1,'methods':'Installed v0.1 Python implementation versus installed v0.2 with explicitly built native backend','cases':records},indent=2)+'\n',encoding='utf-8',newline='\n')
if __name__=='__main__':main()
