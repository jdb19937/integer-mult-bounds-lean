module

public import IntegerMultBounds.Schoenhage.Stream
public import IntegerMultBounds.Schoenhage.Cmd
public import IntegerMultBounds.MathlibTM2.Host.WordStream

/-! The streaming rule as a word-program primitive (host program `streamHProg`). Every input tape must
have a current word; the output tape must be at its end. The inputs step
past their current words, and the emitted symbols, which must form whole
words, are appended to the output tape (in extend mode the first of them
continues the output's last word). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a r : ℕ}

/-- The streaming primitive. -/
noncomputable abbrev streamPrim (R : Rule r) (ext : Bool) : Prim a where
  s := r + 2
  pre := StreamPre R ext
  sem := streamSem R ext
  cost σ := time R (σ drv).cur (fun j => (σ (oth j)).cur)
  nQ := Fintype.card R.Q
  prog := MathlibTM2.Host.WordCmd.streamHProg R ext
  hspec := MathlibTM2.Host.WordCmd.stream_hostSpec R ext
  hcalls := MathlibTM2.Host.WordCmd.streamHProg_noCalls R ext

end IntegerMultBounds.Schoenhage
