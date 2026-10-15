#!/usr/bin/env python3
"""Generate kernel-checked rational spanning and dual certificates for every label."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from fractions import Fraction as Q
from generate_pr589_scalar import SHA256
from generate_pr589_copy_ranks import rref, inverse, vec
from generate_pr589_full_replay import tree

OUT = Path('IntegerMultBounds/Networks/Certificates/PR589/Geometry/Dimensions')
NS = 'IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions'
SIZE = 16

def header(imports):
    return ('module\n\n' + ''.join('public import '+s+'\n' for s in imports) +
            '\n/-! Generated exact rational witnesses; all equations are kernel checked. -/\n'
            '@[expose] public section\nnamespace '+NS+'\n')

def end():
    return '\nend '+NS+'\n'

def dispatch(lo, hi, leaf, indent='  '):
    if hi-lo == 1:
        return indent+leaf(lo)+'\n'
    mid = (lo+hi)//2
    return (indent+f'by_cases h{mid} : i < {mid*SIZE}\n'+indent+'·\n'+
            dispatch(lo,mid,leaf,indent+'  ')+indent+'·\n'+
            dispatch(mid,hi,leaf,indent+'  '))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('word',type=Path);a=ap.parse_args()
    data=a.word.read_bytes();assert hashlib.sha256(data).hexdigest()==SHA256
    w=json.loads(gzip.decompress(data));OUT.mkdir(exist_ok=True,parents=True)
    witnesses=[]
    for f,js in enumerate(w['frames']):
        inds=[];basis=[]
        for j in js:
            if len(rref(basis+[w['lines'][j]])[1])>len(basis):
                inds.append(j);basis.append(list(map(Q,w['lines'][j])))
        d=len(basis)
        gram=[[sum(x*y for x,y in zip(u,v))/2 for v in basis] for u in basis]
        inv=inverse(gram) if d else []
        dual=[[sum(inv[i][j]*basis[j][c] for j in range(d)) for c in range(8)] for i in range(d)]
        witnesses.append((inds,dual))
    dims=[len(x[0]) for x in witnesses]
    s=header([NS+'.Model'])+'\ndef value (i : ℕ) : ℕ := '+tree(dims)+'\n'+end()
    (OUT/'Data.lean').write_text(s)
    blocks=[]
    for start in range(0,len(dims),SIZE):
        k=start//SIZE;blocks.append(k);stop=min(start+SIZE,len(dims))
        s=header([NS+'.Data'])
        for f in range(start,stop):
            inds,dual=witnesses[f];d=len(inds)
            iv=vec(inds) if d else 'Fin.elim0'
            dv=('!['+', '.join(vec(r) for r in dual)+']') if d else 'Fin.elim0'
            s+=f'\ndef certificate{f:03} : Certificate {d} := ⟨{f}, {iv}, {dv}⟩\n'
            s+=f'\ntheorem checked{f:03} : certificate{f:03}.Checked := by decide +kernel\n'
            s+=f'\ntheorem dimension{f:03} : Module.finrank ℚ (label {f}) = {d} := certificate{f:03}.dimension checked{f:03}\n'
        s+=f'\ntheorem block{k:03} (i : ℕ) (hl : {start} ≤ i) (hu : i < {stop}) :\n    Module.finrank ℚ (label i) = value i := by\n  interval_cases i\n'
        for f in range(start,stop):s+=f'  · exact dimension{f:03}\n'
        (OUT/f'Block{k:03}.lean').write_text(s+end())
    s=header([NS+f'.Block{k:03}' for k in blocks])
    s+='\n/-- Every literal PR589 label has its actual rational root-span dimension. -/\ntheorem dimension (i : ℕ) (hi : i < 636) : Module.finrank ℚ (label i) = value i := by\n'
    s+=dispatch(0,len(blocks),lambda k:f'exact block{k:03} i (by omega) (by omega)')
    (OUT/'All.lean').write_text(s+end())
    print(f'Generated {len(dims)} rational certificates in {len(blocks)} blocks.')

if __name__=='__main__':main()
