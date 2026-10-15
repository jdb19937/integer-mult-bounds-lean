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
TRACE = 'IntegerMultBounds.Networks.Certificates.T16.Trace'
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
    for group,lo in enumerate(range(0,len(edge_keys),GROUP)):
        text=header([NS+'.Catalog',NS+'.Checker'])
        for i in range(lo,min(lo+GROUP,len(edge_keys))):
            a,b,r=edge_keys[i]
            witness=[spans[b][v] for v in frames[a]]
            text+=f'def witness{i} : Fin frame{a}.rank → ℕ := {vec(witness)}\n'
            text+=f'theorem edge{i}_span : frame{a}.space ≤ frame{b}.space :=\n  frame{a}.inclusion frame{b} witness{i} (by decide)\n'
            text+=f'def edge{i} : CertifiedEdge catalog where\n  old := {a}\n  next := {b}\n  rank := {r}\n  good := by\n    constructor\n    · exact edge{i}_span\n    constructor\n    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]\n      decide\n    · decide\n\n'
        save('Edges'+str(group),text)
    encoded={a*1004+b:i for i,(a,b,r) in enumerate(edge_keys)}
    assert len(encoded)==len(edge_keys)
    text=header([NS+'.Edges'+str(i) for i in range((len(edge_keys)+GROUP-1)//GROUP)])
    text+='def edgeBank (key : ℕ) : CertifiedEdge catalog :=\n  '+tree(sorted(encoded),'key',lambda key:'edge'+str(encoded[key]))+'\n'
    save('EdgeBank',text)
    for ori in ['forward','backward']:
        back=str(ori=='backward').lower()
        chunk_count=(len(programs[ori])+31)//32
        group_count=(chunk_count+31)//32
        for group in range(group_count):
            text=header([NS+'.EdgeBank',TRACE+'.'+ori.capitalize()+str(group)])
            names=[]
            for chunk in range(group*32,min((group+1)*32,chunk_count)):
                name=ori+'Events'+str(chunk);names.append(name)
                text+=f'theorem {name}_checked : checkEvents edgeBank {back} Trace.{name} = true := by decide\n'
            name=ori+'Group'+str(group)
            text+=f'theorem {name}_checked : checkEvents edgeBank {back} Trace.{name}.flatten = true := by\n'
            text+='  rw [checkEvents_flatten]\n'
            text+=f'  simp only [Trace.{name}, List.all_cons, List.all_nil, '+','.join(n+'_checked' for n in names)+', Bool.true_and]\n'
            save(ori.capitalize()+str(group),text)
        text=header([NS+'.'+ori.capitalize()+str(i) for i in range(group_count)]+[TRACE+'.'+ori.capitalize()])
        text+=f'theorem {ori}_checked : checkEvents edgeBank {back} Trace.{ori}Events = true := by\n'
        text+=f'  rw [Trace.{ori}Events, checkEvents_flatten]\n'
        text+=f'  simp only [Trace.{ori}Chunks, List.all_cons, List.all_nil, '+','.join(ori+'Group'+str(i)+'_checked' for i in range(group_count))+', Bool.true_and]\n'
        text+=f'theorem {ori}_geometry (event : Trace.Event) (h : event ∈ Trace.{ori}Events) : EventGood catalog {back} event :=\n  checkEvents_sound edgeBank {back} {ori}_checked event h\n'
        save(ori.capitalize(),text)
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
