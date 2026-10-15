#!/usr/bin/env python3
"""Generate exact rational dual/normal witnesses for the nine retained E8 frames."""
import argparse,gzip,json,hashlib
from pathlib import Path
from fractions import Fraction as Q
from generate_pr589_scalar import SHA256
OUT=Path('IntegerMultBounds/Networks/Certificates/PR589/Geometry')
NS='IntegerMultBounds.Networks.Certificates.PR589.Geometry'
def rref(rows):
 a=[[Q(v) for v in r] for r in rows];p=[];r=0
 for c in range(len(a[0]) if a else 8):
  pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
  if pivot is None:continue
  a[r],a[pivot]=a[pivot],a[r];d=a[r][c];a[r]=[v/d for v in a[r]]
  for i in range(len(a)):
   if i!=r:
    d=a[i][c];a[i]=[v-d*u for v,u in zip(a[i],a[r])]
  p.append(c);r+=1
  if r==len(a):break
 return a,p
def inverse(a):
 n=len(a);rows,piv=rref([r+[Q(int(i==j)) for j in range(n)] for i,r in enumerate(a)])
 assert piv==list(range(n));return [r[n:] for r in rows]
def rat(x):
 x=Q(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator} / {x.denominator})'
def vec(xs):return '!['+', '.join(rat(x) for x in xs)+']'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('word',type=Path);a=ap.parse_args();data=a.word.read_bytes();assert hashlib.sha256(data).hexdigest()==SHA256;w=json.loads(gzip.decompress(data))
 cur=w['start'].copy()
 for sec in ['D','A']:
  for f,t,ss in w[sec]:
   for i in [t]+ss:cur[i]=f
 frames=[cur[q] for q in w['ret']];assert frames==list(range(510,519))
 s='module\n\npublic import IntegerMultBounds.Networks.Certificates.PR589.Geometry.RankCertificate\n\n/-! Generated exact rational witnesses. Lean checks every membership, dual pairing\nand normal equation; dimensions are derived from those checks, not imported. -/\n@[expose] public section\nnamespace '+NS+'\n'
 for k,f in enumerate(frames):
  inds=[];b=[]
  for j in w['frames'][f]:
   if len(rref(b+[w['lines'][j]])[1])>len(b):inds.append(j);b.append(list(map(Q,w['lines'][j])))
  assert len(b)==7
  gram=[[sum(x*y for x,y in zip(u,v))/2 for v in b] for u in b];gi=inverse(gram)
  dual=[[sum(gi[i][j]*b[j][c] for j in range(7)) for c in range(8)] for i in range(7)]
  rows,piv=rref(b);free=next(i for i in range(8) if i not in piv);normal=[Q(0)]*8;normal[free]=1
  for row,p in zip(rows,piv):normal[p]=-row[free]
  assert all(sum(x*y for x,y in zip(normal,w['lines'][j]))==0 for j in w['frames'][f])
  s+=f'\ndef certificate{f} : HyperplaneCertificate :=\n  ⟨{f}, {vec(inds)}, !['+', '.join(vec(r) for r in dual)+'], '+vec(normal)+'⟩\n'
  s+=f'\ntheorem checked{f} : certificate{f}.Checked := by decide +kernel\n'
  s+=f'\ntheorem dimension{f} : Module.finrank ℚ (label {f}) = 7 := certificate{f}.dimension checked{f}\n'
  s+=f'\ntheorem copy_rank{f} : Module.finrank ℚ (LinearMap.range (-projector {f})) = 7 := certificate{f}.copy_rank checked{f}\n'
 s+='\ntheorem copy_source_frames : Copy.lifecycles.map Copy.Lifecycle.sourceFrame = ['+', '.join(map(str,frames))+'] := by decide +kernel\n'
 s+='\n/-- Sum of ranks of the actual nine inverse-projector COPY operators. -/\ntheorem copy_rank_sum : (Copy.lifecycles.map (fun life => Module.finrank ℚ (LinearMap.range (-projector life.sourceFrame)))).sum = 63 := by\n  have h := congrArg (fun fs : List ℕ => (fs.map (fun f => Module.finrank ℚ (LinearMap.range (-projector f)))).sum) copy_source_frames\n  simpa [List.map_map, Function.comp_def, '+', '.join(f'copy_rank{f}' for f in frames)+'] using h\n'
 s+='\nend '+NS+'\n';OUT.mkdir(exist_ok=True,parents=True);(OUT/'CopyRanks.lean').write_text(s);print('Generated nine exact rational dual/normal certificates.')
if __name__=='__main__':main()
