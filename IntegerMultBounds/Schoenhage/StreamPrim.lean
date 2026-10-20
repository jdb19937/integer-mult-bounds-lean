module

public import IntegerMultBounds.Schoenhage.Stream
public import IntegerMultBounds.Schoenhage.Cmd
public import IntegerMultBounds.MathlibTM2.Host.WordStream

/-! The streaming machine as a word-program primitive. Every input tape must
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
  hs := by omega
  M := machine R ext
  pre := StreamPre R ext
  sem := streamSem R ext
  cost σ := time R (σ drv).cur (fun j => (σ (oth j)).cur)
  nQ := Fintype.card R.Q
  prog := MathlibTM2.Host.WordCmd.streamHProg R ext
  hspec := MathlibTM2.Host.WordCmd.stream_hostSpec R ext
  hcalls := MathlibTM2.Host.WordCmd.streamHProg_noCalls R ext
  spec σ hpre := by
    obtain ⟨hdrv, hoth, hout, vs, hvs, hext⟩ := hpre
    apply FMachine.hoare
    intro v hv
    subst hv
    obtain ⟨w, R0, hw⟩ := exists_cons hdrv
    have hRd : Rd ((enc (a := a) σ).tape drv) ((enc (a := a) σ).head drv) (σ drv).cur := by
      simpa [enc, WTape.cur, hw] using (σ drv).Rd_of (a := a) hw
    have hRo : ∀ j, Rd ((enc (a := a) σ).tape (oth j)) ((enc (a := a) σ).head (oth j)) (σ (oth j)).cur :=
      fun j => by
        obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simpa [enc, WTape.cur, hw'] using (σ (oth j)).Rd_of (a := a) hw'
    obtain ⟨v', hrun, hhalt, htape, hhdrv, hhoth, hhout⟩ := stream_run R ext (enc σ) _ _ hRd hRo
    refine ⟨_, _, le_rfl, hrun, hhalt, ?_⟩
    simp only []
    rw [hvs] at htape hhout
    have hsem_out : streamSem R ext σ out = (σ out).put ext vs := by
      simp [streamSem, hvs, parse_syms]
    refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
    · rcases cases_tape i with rfl | ⟨j, rfl⟩ | rfl
      · rw [hhdrv]; simp only [enc, streamSem, drv_ne_out, ↓reduceIte]
        rw [(σ drv).next_pos hw]; simp [WTape.cur, hw]
      · rw [hhoth]
        obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simp only [enc, streamSem, oth_ne_out, ↓reduceIte]
        rw [(σ (oth j)).next_pos hw']; simp [WTape.cur, hw']
      · rw [hhout]; simp only [enc, hsem_out]
        cases ext with
        | false =>
          simp [WTape.put, WTape.pos, clen_append, clen_reverse, length_syms]; ring
        | true =>
          obtain ⟨hL, hV⟩ := hext rfl
          obtain ⟨u, L, hl⟩ := exists_cons hL
          obtain ⟨x, xs, hx⟩ := exists_cons hV
          subst hx
          simp [WTape.put, hl, WTape.pos, clen_append, clen_reverse, length_syms]; ring
    · rw [htape]
      rcases cases_tape i with rfl | ⟨j, rfl⟩ | rfl
      · simp only [drv_ne_out, ↓reduceIte, enc, streamSem]; rw [(σ drv).next_tape hw]
      · obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simp only [oth_ne_out, ↓reduceIte, enc, streamSem]; rw [(σ (oth j)).next_tape hw']
      · simp only [↓reduceIte, enc, hsem_out]
        cases ext with
        | false =>
          have := (σ out).put_end (a := a) hout vs
          simpa [WTape.put, cells] using this
        | true =>
          obtain ⟨hL, hV⟩ := hext rfl
          obtain ⟨u, L, hl⟩ := exists_cons hL
          obtain ⟨x, xs, hx⟩ := exists_cons hV
          subst hx
          have := (σ out).put_ext (a := a) hl hout x xs
          simpa [WTape.put, hl, cells] using this

end IntegerMultBounds.Schoenhage
