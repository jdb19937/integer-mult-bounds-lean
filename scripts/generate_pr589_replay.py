#!/usr/bin/env python3
"""Generate the next small PR589 scalar checkpoint without modifying the import."""
import gzip, hashlib, json
from pathlib import Path
import argparse
from generate_pr589_scalar import SHA256, OUT, NS, header

def main():
    ap=argparse.ArgumentParser();ap.add_argument('word',type=Path);a=ap.parse_args()
    data=a.word.read_bytes();assert hashlib.sha256(data).hexdigest()==SHA256
    w=json.loads(gzip.decompress(data));state=[1<<i for i in range(661)]
    text=header([NS+'.FirstCheckpoint'])
    for count in [4,20]:
        state=[1<<i for i in range(661)]
        for _,t,ss in w['D'][:count]:
            for i in ss:state[t]^=state[i]
        for i in range(111,111+count):
            text+=f'\ndef d{count}row{i} : BitVec 661 := BitVec.ofNat 661 {state[i]}\n'
        text+=f'\ndef checkpointD{count} (i : ℕ) : BitVec 661 :=\n'
        for i in range(111,111+count):text+=f'  if i = {i} then d{count}row{i} else\n'
        text+='  initial i\n'
    text+='\ndef secondChunk : List RawGate := (sectionD.drop 4).take 16\n'
    text+='\ntheorem second_bounds : secondChunk.all RawGate.bounded = true := by decide +kernel\n'
    for i in range(115,131):
        text+=f'\ntheorem second_row_{i} : replay secondChunk checkpointD4 {i} = d20row{i} := by decide +kernel\n'
    text+='\ntheorem second_preserves (i : ℕ) (h : i < 115 ∨ 131 ≤ i) :\n    replay secondChunk checkpointD4 i = checkpointD4 i := by\n  apply replay_preserves\n  intro g hg\n  change g ∈ ['+', '.join(f'sectionDGate{i:04}' for i in range(4,20))+'] at hg\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with '+' | '.join(['rfl']*16)+' <;> simp only ['+', '.join(f'sectionDGate{i:04}' for i in range(4,20))+'] <;> omega\n'
    text+='\ntheorem first_replay : replay (sectionD.take 4) initial = checkpointD4 := by\n  funext i\n'
    for i in range(111,115):
        text+=f'  by_cases h{i} : i = {i}\n  · subst i\n    exact first_four_row_{i}\n'
    text+='  rw [first_four_preserves i (by omega)]\n  simp only [checkpointD4, '+', '.join(f'if_neg h{i}' for i in range(111,115))+']\n'
    text+='\ntheorem second_replay : replay secondChunk checkpointD4 = checkpointD20 := by\n  funext i\n'
    for i in range(115,131):
        text+=f'  by_cases h{i} : i = {i}\n  · subst i\n    exact second_row_{i}\n'
    text+='  rw [second_preserves i (by omega)]\n  simp only [checkpointD4, checkpointD20, '+', '.join(f'if_neg h{i}' for i in range(115,131))+']\n  rfl\n'
    text+='\ntheorem first_twenty_replay : replay (sectionD.take 20) initial = checkpointD20 := by\n  change replay ((sectionD.take 4) ++ secondChunk) initial = checkpointD20\n  rw [replay_append, first_replay, second_replay]\n'
    text+=f'\nend {NS}\n'
    (OUT/'SecondCheckpoint.lean').write_text(text)
if __name__=='__main__':main()
