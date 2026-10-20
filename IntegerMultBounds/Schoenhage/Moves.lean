module

public import IntegerMultBounds.Schoenhage.Cmd

/-! Head movements on one word tape as word-program primitives: rewind to the first word, step
back over the previous word, erase the whole tape, and append fixed words. Each runs on host
stacks by its host program (`Host/WordTape`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

variable {a : ℕ}

namespace Rewind

/-- Rewind: all words to the right of the head. -/
noncomputable abbrev prim : Prim a where
  s := 1
  pre _ := True
  sem σ := fun _ => ⟨[], (σ 0).left.reverse ++ (σ 0).right⟩
  cost σ := clen (σ 0).left + 2
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.rewindProg
  hspec := MathlibTM2.Host.WordCmd.rewind_hostSpec
  hcalls := MathlibTM2.Host.WordCmd.rewindProg_noCalls

end Rewind

namespace Back

/-- Back: the previous word becomes current. -/
noncomputable abbrev prim : Prim a where
  s := 1
  pre σ := (σ 0).left ≠ []
  sem σ := fun _ => ⟨(σ 0).left.tail, (σ 0).left.headD [] :: (σ 0).right⟩
  cost σ := ((σ 0).left.headD []).length + 3
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.backProg
  hspec := MathlibTM2.Host.WordCmd.back_hostSpec
  hcalls := MathlibTM2.Host.WordCmd.backProg_noCalls

end Back

namespace Clear

/-- Clear: erase the whole tape. -/
noncomputable abbrev prim : Prim a where
  s := 1
  pre _ := True
  sem _ := fun _ => ⟨[], []⟩
  cost σ := 2 * clen (σ 0).words + 2
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.clearProg
  hspec := MathlibTM2.Host.WordCmd.clear_hostSpec
  hcalls := MathlibTM2.Host.WordCmd.clearProg_noCalls

end Clear

namespace Emit

/-- Emit: append fixed words at the end of the tape. -/
noncomputable abbrev prim (ws : List (List Bool)) : Prim a where
  s := 1
  pre σ := (σ 0).right = []
  sem σ := fun _ => ⟨ws.reverse ++ (σ 0).left, []⟩
  cost _ := clen ws
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.emitProg ws
  hspec := MathlibTM2.Host.WordCmd.emit_hostSpec ws
  hcalls := MathlibTM2.Host.WordCmd.emitProg_noCalls ws

end Emit

end IntegerMultBounds.Schoenhage
