#!/usr/bin/env python3
"""Import exact selected T16 binary frames and finite inclusion witnesses.

The source files are read-only hash-pinned data; no supplier program executes.
"""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / 'IntegerMultBounds/Networks/Certificates/T16/Geometry'
NS = 'IntegerMultBounds.Networks.Certificates.T16.Geometry'
LOCAL = 'research/r480-owner-optimum/inputs/local'
PINS = {
    'CANONICAL-WORD.json.gz': '16bc0ebb04b4be6c0ade74badc6a0c0cdba4215eda86e4ff9f13abf8ecebd219',
    'LOCAL-PROGRAMS.json.gz': '241fde27d4e43f5a9cb6b128f9f76c5131a53d09f0371676163f914d0b0fef3a',
}
GROUP = 32

def header(imports):
    return 'module\n\n' + ''.join('public import '+i+'\n' for i in imports) + '\n/-! Generated from the exact pinned T16 native frame catalog. -/\n@[expose] public section\nnamespace '+NS+'\n\n'

def vec(xs, mask=False):
    return '!['+','.join((str(x)+'#9') if mask else str(x) for x in xs)+']'

def parity(x):
    return x.bit_count() % 2

def tree(rows, variable, value):
    if len(rows) == 1:
        return value(rows[0])
    mid = len(rows)//2
    return f'(if {variable} < {rows[mid]} then '+tree(rows[:mid],variable,value)+' else '+tree(rows[mid:],variable,value)+')'

def main():
    if sys.flags.optimize:
        raise SystemExit('Schema assertions must remain enabled')
    ap = argparse.ArgumentParser()
    ap.add_argument('source', type=Path)
    ap.add_argument('--output', type=Path, default=DEFAULT_OUT)
    ap.add_argument('--probe', action='store_true')
    args = ap.parse_args()
    data = {}
    for name,digest in PINS.items():
        raw=(args.source/LOCAL/name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest:
            raise SystemExit('Pinned hash mismatch: '+name)
        data[name]=json.loads(gzip.decompress(raw))
    frames=data['CANONICAL-WORD.json.gz']['frames']
    programs=data['LOCAL-PROGRAMS.json.gz']
    assert len(frames)==1004
    duals=[];spans=[]
    for basis in frames:
        assert len(basis)<=9 and all(type(x) is int and 0<=x<512 for x in basis)
        duals.append([next(d for d in range(512) if all(parity(d & v)==int(i==j) for j,v in enumerate(basis))) for i in range(len(basis))])
        span={}
        for selection in range(1<<len(basis)):
            value=0
            for i,v in enumerate(basis):
                if selection>>i&1:value^=v
            assert value not in span
            span[value]=selection
        spans.append(span)
    edge_keys=set()
    for ori in ['forward','backward']:
        for e in programs[ori]:
            if e[0]=='climb':a,b,r=e[3:]
            elif e[0]=='center':
                a,b,r=e[2:]
                if ori=='forward':a,b=b,a
            else:continue
            assert 0<=a<1004 and 0<=b<1004 and r==len(frames[b])-len(frames[a]) and r>0
            assert all(v in spans[b] for v in frames[a])
            edge_keys.add((a,b,r))
    edge_keys=sorted(edge_keys)
    assert len(edge_keys)==2888
    args.output.mkdir(parents=True,exist_ok=True)
    def save(name,text):
        (args.output/(name+'.lean')).write_text(text+'\nend '+NS+'\n')
    for group,lo in enumerate(range(0,len(frames),GROUP)):
        text=header([NS+'.Model'])
        for i in range(lo,min(lo+GROUP,len(frames))):
            text+=f'def frame{i} : Frame := ⟨{len(frames[i])}, {vec(frames[i],True)}, {vec(duals[i],True)}⟩\n'
            text+=f'theorem frame{i}_dual : frame{i}.DualCheck := by decide\n'
            text+=f'def checkedFrame{i} : CertifiedFrame := ⟨frame{i}, frame{i}.independent frame{i}_dual⟩\n\n'
        save('Frames'+str(group),text)
        if args.probe:return
    text=header([NS+'.Frames'+str(i) for i in range((len(frames)+GROUP-1)//GROUP)])
    text+='def catalog (i : ℕ) : CertifiedFrame :=\n  if i < 1004 then '+tree(list(range(1004)),'i',lambda i:'checkedFrame'+str(i))+' else checkedFrame0\n'
    text+='theorem catalog_independent (i : ℕ) : LinearIndependent F (catalog i).data.vectors := (catalog i).independent\n'
    text+='theorem catalog_dimension (i : ℕ) : Module.finrank F (catalog i).space = (catalog i).data.rank := (catalog i).dimension\n'
    save('Catalog',text)
    # Checker.lean decides span inclusion from the catalog; Forward.lean and Backward.lean are
    # hand-written. The edge assertions above still validate the supplier data.
    (args.output/'geometry-provenance.json').write_text(json.dumps({
        'source_directory':LOCAL,'pins':PINS,'frame_count':len(frames),
        'distinct_oriented_edges':len(edge_keys),'ambient_binary_dimension':9,
        'events_per_orientation':{ori:len(programs[ori]) for ori in ['forward','backward']},
        'event_hashes':{ori:hashlib.sha256(json.dumps(programs[ori],separators=(',',':')).encode()).hexdigest() for ori in ['forward','backward']},
        'encoding':'Low-bit-first nine-bit masks; raw ordered bases retained. Dual and XOR witnesses checked in Lean.',
        'licenses_and_notices':'../Trace/ (byte-identical pinned original notices retained in trace-provenance.json)',
        'scope':'Actual binary span independence, inclusion and finite-dimensional rank differences for exact retained native climb/center events. No ambient frame operators, adapter semantics, dirty scalar endpoint, hosting or tape cost.'
    },indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
