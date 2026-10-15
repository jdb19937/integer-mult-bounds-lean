#!/usr/bin/env python3
"""Generate shallow, kernel-checkable PR589 scalar checkpoints (24 gates each)."""
import argparse,gzip,json,hashlib
from pathlib import Path
from generate_pr589_scalar import SHA256,OUT,NS,header

def tree(values,lo=0):
    if len(values)==1:return str(values[0])
    m=len(values)//2
    return f'(if i < {lo+m} then {tree(values[:m],lo)} else {tree(values[m:],lo+m)})'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('word',type=Path);a=ap.parse_args()
    data=a.word.read_bytes();assert hashlib.sha256(data).hexdigest()==SHA256
    w=json.loads(gzip.decompress(data));sections={s:w[s] for s in ['D','A','B','C']}
    sections['scatter']=[[0,111+t,[w['ret'][k] for k in ks]] for t,ks in enumerate(w['scatter'])]
    masks=[1<<i for i in range(661)];known={x:i for i,x in enumerate(masks)};refs=list(range(661));chunks=[]
    for sec in ['D','A','scatter','B','C']:
        for offset in range(0,len(sections[sec]),24):
            gs=sections[sec][offset:offset+24];before=refs.copy()
            for _,t,ss in gs:
                value=masks[refs[t]]
                for i in ss:value^=masks[refs[i]]
                if value not in known:known[value]=len(masks);masks.append(value)
                refs[t]=known[value]
            chunks.append((sec,offset//24,gs,before,refs.copy()))
    text=header([NS+'.Checkpoint'])
    for i,m in enumerate(masks):text+=f'\ndef mask{i:04} : BitVec 661 := BitVec.ofNat 661 {m}\n'
    blocknames=[]
    for start in range(0,len(masks),32):
        name=f'maskBlock{start//32:03}';blocknames.append(name+' i')
        text+=f'\ndef {name} (i : ℕ) : BitVec 661 := '+tree([f'mask{i:04}' for i in range(start,min(start+32,len(masks)))],start)+'\n'
    # Dispatch on block number separately: leaf helpers use the original index.
    text+='\ndef maskBank (i : ℕ) : BitVec 661 :=\n  let block := i / 32\n'+tree(blocknames).replace('if i <','if block <')+'\n'
    text+=f'\nend {NS}\n';(OUT/'MaskBank.lean').write_text(text)
    for k,(sec,j,gs,before,after) in enumerate(chunks):
        name=f'Replay{k:03}';chunk=f'section{sec}Chunk{j:03}';targets=[g[1] for g in gs]
        text=header([NS+'.MaskBank',NS+'.'+sec])
        text+=f'\ndef refsBefore{k:03} (i : ℕ) : ℕ := '+tree(before)+'\n'
        text+=f'\ndef refsAfter{k:03} (i : ℕ) : ℕ := '+tree(after)+'\n'
        text+=f'\ntheorem offTargets{k:03} : offTargetCheck ({chunk}.map RawGate.target) refsBefore{k:03} refsAfter{k:03} = true := by\n  decide +kernel\n'
        for t in sorted(set(targets)):
            text+=f'\ntheorem row{k:03}_{t} : replay {chunk} (snapshot maskBank refsBefore{k:03}) {t} = snapshot maskBank refsAfter{k:03} {t} := by\n  decide +kernel\n'
        text+=f'\ntheorem replay{k:03} : replay {chunk} (snapshot maskBank refsBefore{k:03}) = snapshot maskBank refsAfter{k:03} := by\n  apply checkpoint maskBank _ _ _ offTargets{k:03}\n  intro i hi\n  change i ∈ ['+', '.join(map(str,targets))+'] at hi\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi\n  rcases hi with '+' | '.join(['rfl']*len(targets))+'\n'
        for t in targets:text+=f'  · exact row{k:03}_{t}\n'
        text+=f'\nend {NS}\n';(OUT/(name+'.lean')).write_text(text)
    for sec in ['D','A','scatter','B','C']:
        ks=[k for k,c in enumerate(chunks) if c[0]==sec]
        text=header([NS+f'.Replay{k:03}' for k in ks])
        text+=f'\ntheorem replaySection{sec} : replay section{sec} (snapshot maskBank refsBefore{ks[0]:03}) = snapshot maskBank refsAfter{ks[-1]:03} := by\n  simp only [section{sec}, replay_append]\n'
        for pos,k in enumerate(ks):
            if pos:
                text+=f'  have link{k:03} : snapshot maskBank refsAfter{k-1:03} = snapshot maskBank refsBefore{k:03} := rfl\n  rw [link{k:03}]\n'
            text+=f'  rw [replay{k:03}]\n'
        text+=f'\nend {NS}\n';(OUT/('ReplaySection'+sec+'.lean')).write_text(text)
    text=header([NS+'.Word']+[NS+'.ReplaySection'+s for s in ['D','A','scatter','B','C']])
    text+='\ntheorem full_scalar_replay : replay program (snapshot maskBank refsBefore000) = snapshot maskBank refsAfter234 := by\n  simp only [program, replay_append]\n'
    for sec in ['D','A','scatter','B','C']:
        ks=[k for k,c in enumerate(chunks) if c[0]==sec]
        if ks[0]:text+=f'  have link{sec} : snapshot maskBank refsAfter{ks[0]-1:03} = snapshot maskBank refsBefore{ks[0]:03} := rfl\n  rw [link{sec}]\n'
        text+=f'  rw [replaySection{sec}]\n'
    text+=f'\nend {NS}\n';(OUT/'FullReplay.lean').write_text(text)
    text=header([NS+'.Replay000',NS+'.Replay234'])
    text+='\ntheorem initial_mask_rows : ∀ i : Fin 661, snapshot maskBank refsBefore000 i.val = initial i.val := by\n  decide +kernel\n'
    text+='\ntheorem final_mask_rows : ∀ i : Fin 661, snapshot maskBank refsAfter234 i.val =\n    if 111 ≤ i.val ∧ i.val < 222 then initial i.val ^^^ initial (i.val - 111) else initial i.val := by\n  decide +kernel\n'
    text+=f'\nend {NS}\n';(OUT/'EndpointMasks.lean').write_text(text)
    text=header([NS+'.Word'])
    for k,(sec,j,_,_,_) in enumerate(chunks):
        text+=f'\ntheorem bounds{k:03} : section{sec}Chunk{j:03}.all RawGate.bounded = true := by decide +kernel\n'
    text+='\ntheorem program_bounded : program.all RawGate.bounded = true := by\n  simp only [program, sectionD, sectionA, sectionscatter, sectionB, sectionC, List.all_append, '+', '.join(f'bounds{k:03}' for k in range(len(chunks)))+', Bool.and_self]\n'
    text+=f'\nend {NS}\n';(OUT/'Bounds.lean').write_text(text)
    text=header([NS+'.Word'])
    text+='\ndef sourceAdditions (gs : List RawGate) : ℕ := (gs.map (fun g => g.sources.length)).sum\n'
    text+='\ntheorem sourceAdditions_append (left right : List RawGate) : sourceAdditions (left ++ right) = sourceAdditions left + sourceAdditions right := by simp [sourceAdditions, List.map_append, List.sum_append]\n'
    for k,(sec,j,gs,_,_) in enumerate(chunks):
        text+=f'\ntheorem additions{k:03} : sourceAdditions section{sec}Chunk{j:03} = {sum(len(g[2]) for g in gs)} := by decide +kernel\n'
    total=sum(len(g[2]) for sec in ['D','A','scatter','B','C'] for g in sections[sec])
    text+=f'\n/-- Exact scalar additions after expanding each multi-source update. This is not a tape-step bound. -/\ntheorem source_addition_count : sourceAdditions program = {total} := by\n  simp only [program, sectionD, sectionA, sectionscatter, sectionB, sectionC, sourceAdditions_append, '+', '.join(f'additions{k:03}' for k in range(len(chunks)))+']\n'
    text+=f'\nend {NS}\n';(OUT/'Counts.lean').write_text(text)
    print(f'Generated {len(chunks)} independent checkpoints, {len(masks)} distinct masks; full chain assembly still required.')
if __name__=='__main__':main()
