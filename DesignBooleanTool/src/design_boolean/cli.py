"""Command-line entry point. Exit codes: 0 success, 1 rejection, 2 bad input, 3 unsupported, 4 backend error."""
import argparse
import json
import sys
from .core import recognize,verify_certificate
from .boolean import BooleanFunction
from .io import load_incidence,read_text,write_json,DEFAULT_MAX_CELLS,DEFAULT_MAX_BYTES

def parser():
    p=argparse.ArgumentParser(prog="design-boolean",description="Recognize binary designs and reconstruct plateaued Boolean functions with checkable certificates.")
    p.add_argument("--version",action="version",version="design-boolean 0.2.0")
    sub=p.add_subparsers(dest="command",required=True)
    sub.add_parser("build-native",help="Explicitly build the optional native backend with a C++ compiler.")
    for command in ("recognize","verify"):
        s=sub.add_parser(command)
        s.add_argument("input",help="Point-row incidence JSON/CSV, .gz supported; or JSON point_count plus blocks.")
        s.add_argument("--max-cells",type=int,default=DEFAULT_MAX_CELLS)
        s.add_argument("--max-bytes",type=int,default=DEFAULT_MAX_BYTES)
        s.add_argument("-o","--output",help="Write JSON here instead of stdout.")
        if command=="recognize":
            s.add_argument("--backend",choices=("auto","python","native"),default="auto")
            s.add_argument("--certificate-out",help="Also save the standalone reconstruction certificate.")
            s.add_argument("--function-out",help="Also save the reconstructed truth table, ANF and Walsh statistics.")
        else:
            s.add_argument("certificate",help="Standalone certificate JSON or recognition-result JSON.")
    return p

def main(argv=None):
    args=parser().parse_args(argv)
    try:
        if args.command=="build-native":
            from .native import build_native
            library=build_native()
            write_json({"status":"built","library":str(library)})
            return 0
        if args.max_cells<1 or args.max_bytes<1:
            raise ValueError("Input limits must be positive.")
        prefer_dense=False
        if args.command=="recognize" and args.backend!="python":
            from . import native
            prefer_dense=args.backend=="native" or native.available()
        matrix,labels=load_incidence(args.input,max_cells=args.max_cells,max_bytes=args.max_bytes,packed=not prefer_dense)
        if args.command=="recognize":
            result=recognize(matrix,backend=args.backend,**labels)
            value=result.to_dict()
            write_json(value,args.output)
            if value["status"]=="recognized":
                cert=value["certificate"]
                if args.certificate_out:
                    write_json(cert,args.certificate_out)
                if args.function_out:
                    write_json(BooleanFunction(tuple(cert["truth_table"])).to_dict(),args.function_out)
            return {"recognized":0,"not_recognized":1,"invalid_input":2,"unsupported":3}.get(value["status"],2)
        data=json.loads(read_text(args.certificate,args.max_bytes))
        cert=data.get("certificate",data) if isinstance(data,dict) else data
        verification=verify_certificate(matrix,cert)
        value=verification.to_dict()
        write_json(value,args.output)
        return 0 if value["valid"] else 1
    except RuntimeError as exc:
        print(json.dumps({"status":"backend_error","reason":str(exc)},ensure_ascii=True),file=sys.stderr)
        return 4
    except (ValueError,TypeError,KeyError,OSError,OverflowError) as exc:
        print(json.dumps({"status":"invalid_input","reason":str(exc)},ensure_ascii=True),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
