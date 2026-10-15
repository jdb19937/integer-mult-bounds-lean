#!/usr/bin/env python3
"""Reconstruct and certify the exact greedy binary extensions; never execute supplier code."""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'IntegerMultBounds/Networks/Certificates/T16'
NS = 'IntegerMultBounds.Networks.Certificates.T16.Tableau'
IMPORT = 'IntegerMultBounds.Networks.Certificates.T16'
WORD = 'research/r480-owner-optimum/inputs/local/CANONICAL-WORD.json.gz'
COMPILER = 'research/complex-sw4-frame8/vendor/main/research/complex-k492-owner-repair/vendor/multicold/vendor/pr558/vendor/pr552/complex-global/vendor531/vendor/clifford/clifford_exact.py'
PINS = {WORD:'16bc0ebb04b4be6c0ade74badc6a0c0cdba4215eda86e4ff9f13abf8ecebd219',COMPILER:'2982ead07721e83358dc67c6f49c2b4c16a236a6bebdfd72f58221be1f5d0962'}

def vec(xs):return '!['+','.join(str(x)+'#9' for x in xs)+']'
def tree(ids):
    if len(ids)==1:return f'⟨checkedFrame{ids[0]}, extension{ids[0]}⟩'
    mid=len(ids)//2
    return f'(if i < {ids[mid]} then {tree(ids[:mid])} else {tree(ids[mid:])})'
def tree_proof(ids):
    if len(ids)==1:return 'rfl'
    mid=len(ids)//2
    return f'(select_frame {tree_proof(ids[:mid])} {tree_proof(ids[mid:])})'
def header(imports):
    return 'module\n\n'+''.join('public import '+x+'\n' for x in imports)+'\n/-! Generated from pinned source data and the exact greedy extension rule. -/\n@[expose] public section\nnamespace '+NS+'\nopen Geometry\n\n'

def main():
    if sys.flags.optimize:raise SystemExit('Schema assertions must remain enabled')
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,default=OUT);ap.add_argument('--probe',action='store_true');args=ap.parse_args()
    raw={}
    for path,digest in PINS.items():
        raw[path]=(args.source/path).read_bytes()
        if hashlib.sha256(raw[path]).hexdigest()!=digest:raise SystemExit('Pinned hash mismatch: '+path)
    frames=json.loads(gzip.decompress(raw[WORD]))['frames'];assert len(frames)==1004
    matrices=[]
    for frame in frames:
        assert len(frame)<=9 and all(type(x)is int and 0<=x<512 for x in frame)
        cols=[];span={0}
        for x in frame+[1<<i for i in range(9)]:
            if x not in span:
                cols.append(x);span|={x^v for v in span}
        assert len(cols)==9 and len(span)==512 and cols[:len(frame)]==frame
        dual=[next(d for d in range(512) if all((d&v).bit_count()%2==int(i==j) for j,v in enumerate(cols))) for i in range(9)]
        matrices.append((cols,dual))
    args.output.mkdir(parents=True,exist_ok=True)
    def save(name,text):(args.output/(name+'.lean')).write_text(text+'\nend '+NS+'\n')
    for group,lo in enumerate(range(0,1004,32)):
        text=header([IMPORT+'.TableauFramesModel'])
        for i in range(lo,min(lo+32,1004)):
            cols,dual=matrices[i]
            text+=f'def matrix{i} : MatrixWitness := ⟨{vec(cols)}, {vec(dual)}⟩\n'
            text+=f'theorem matrix{i}_dual : matrix{i}.DualCheck := by decide\n'
            text+=f'noncomputable def extension{i} : FrameExtension frame{i} :=\n  matrix{i}.extension matrix{i}_dual frame{i} (by decide) (by decide)\n\n'
        save('TableauFrames'+str(group),text)
        if args.probe:return
    text=header([IMPORT+'.TableauFrames'+str(i) for i in range(32)])
    text+='noncomputable def sourceBank (i : ℕ) : (f : CertifiedFrame) × FrameExtension f.data :=\n  if i < 1004 then '+tree(list(range(1004)))+' else ⟨checkedFrame0, extension0⟩\n'
    text+='theorem select_frame {p : Prop} [Decidable p]\n    {a b : (f : CertifiedFrame) × FrameExtension f.data} {u v : CertifiedFrame}\n    (ha : a.1 = u) (hb : b.1 = v) :\n    (if p then a else b).1 = (if p then u else v) := by split <;> assumption\n'
    text+='theorem sourceBank_frame (i : ℕ) : (sourceBank i).1 = catalog i := by\n  unfold sourceBank catalog\n  exact select_frame '+tree_proof(list(range(1004)))+' rfl\n'
    text+='noncomputable def catalogExtension (i : ℕ) : FrameExtension (catalog i).data := by\n  rw [← sourceBank_frame i]\n  exact (sourceBank i).2\n'
    text+='noncomputable def nativeTableau (i : ℕ) : PhaseAddress ≃ₗ[F] PhaseAddress :=\n  sourceCanonical (catalogExtension i).matrix (catalog i).data.rank\n'
    save('TableauFramesCatalog',text)
    (args.output/'tableau-frames-provenance.json').write_text(json.dumps({'pins':PINS,'frame_count':1004,'dimension':9,'selection':'Greedily retain original ordered columns, then standard units in increasing bit order iff outside the accumulated XOR span.','inverse_witness':'Unique dual masks, equal to the inverse matrix rows.','scope':'Actual invertible source extension matrices and initial-column retention; binary tableaus only. No complex operator or phase proof.'},indent=2,sort_keys=True)+'\n')
if __name__=='__main__':main()
