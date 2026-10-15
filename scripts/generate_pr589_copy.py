#!/usr/bin/env python3
"""Import nine COPY/ADD/ERASE lifecycles, preserving exporter source-major order."""
import argparse,gzip,hashlib,json
from pathlib import Path
from generate_pr589_scalar import SHA256
EXPORTER_SHA='8a5999601f917dbb492bb9ae9a344611f18cc7cedc53dc3c76496a369e530eb3'
OUT=Path('IntegerMultBounds/Networks/Certificates/PR589/Copy')
NS='IntegerMultBounds.Networks.Certificates.PR589.Copy'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('word',type=Path);ap.add_argument('exporter',type=Path);a=ap.parse_args()
 assert hashlib.sha256(a.word.read_bytes()).hexdigest()==SHA256
 assert hashlib.sha256(a.exporter.read_bytes()).hexdigest()==EXPORTER_SHA
 w=json.loads(gzip.decompress(a.word.read_bytes()));cur=w['start'].copy()
 for sec in ['D','A']:
  for f,t,ss in w[sec]:
   for i in [t]+ss:cur[i]=f
 s='module\n\npublic import IntegerMultBounds.Networks.Certificates.PR589.Copy.Model\n\n/-! Generated from pinned PR589 word and hash-checked export_records.py.\nNine COPY/ERASE windows reuse temporary register661;527 ADDs are separate. -/\n@[expose] public section\nnamespace '+NS+'\n'
 for k,q in enumerate(w['ret']):
  targets=[111+t for t,row in enumerate(w['scatter']) if k in row]
  s+=f'\ndef life{k} : Lifecycle := ⟨{q}, {cur[q]}, ['+', '.join(map(str,targets))+']⟩\n'
 s+='\ndef lifecycles : List Lifecycle := ['+', '.join(f'life{k}' for k in range(9))+']\n'
 s+='\ntheorem copy_count : lifecycles.length = 9 := by decide +kernel\n'
 s+='\ntheorem add_count : (lifecycles.map (fun l => l.targets.length)).sum = 527 := by decide +kernel\n'
 s+='\ntheorem record_count : 2 * lifecycles.length + (lifecycles.map (fun l => l.targets.length)).sum = 545 := by decide +kernel\n'
 s+='\ntheorem wellformed : ∀ life ∈ lifecycles, life.targets.Nodup ∧ 661 ∉ life.targets ∧\n    Frames.beforeScatter life.source = life.sourceFrame ∧\n    ∀ i ∈ life.targets, Frames.beforeScatter i = 0 := by decide +kernel\n'
 s+='\ntheorem source_bounds : ∀ life ∈ lifecycles, 222 ≤ life.source ∧ life.source < 661 := by decide +kernel\n'
 s+='\ntheorem target_bounds : ∀ life ∈ lifecycles, ∀ i ∈ life.targets, 111 ≤ i ∧ i < 222 := by decide +kernel\n'
 s+='\ntheorem source_order : lifecycles.map Lifecycle.source = Frames.retained := by decide +kernel\n'
 s+='\nend '+NS+'\n';OUT.mkdir(exist_ok=True,parents=True);(OUT/'Data.lean').write_text(s)
 print('Generated nine lifecycles,527 ADD incidences,545 COPY/ADD/ERASE records.')
if __name__=='__main__':main()
