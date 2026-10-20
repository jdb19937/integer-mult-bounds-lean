module

public import IntegerMultBounds.Schoenhage.Ops
public import IntegerMultBounds.MathlibTM2.Host.WordCopy

/-! Copying a word reversed, as a primitive (`Reverse.prim`, `revw`; host program
`reverseProg`): the source advances one word and the destination gains the reversed word
(`runs_revw`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

namespace Reverse

/-- Reverse: the source's current word, reversed, as a new word of the destination. -/
noncomputable abbrev prim : Prim where
  s := 2
  pre σ := (σ 0).right ≠ [] ∧ (σ 1).right = []
  sem σ := fun i => if i.val = 0 then (σ 0).next else ⟨(σ 0).cur.reverse :: (σ 1).left, []⟩
  cost σ := 3 * (σ 0).cur.length + 10
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.reverseProg
  hspec := MathlibTM2.Host.WordCmd.reverse_hostSpec
  hcalls := MathlibTM2.Host.WordCmd.reverseProg_noCalls

end Reverse

/-- Two slots: source then destination. -/
def slotRev (s d : Fin t) : Fin 2 → Fin t := fun i => if i.val = 0 then s else d

theorem slotRev_inj {s d : Fin t} (h : s ≠ d) : Function.Injective (slotRev s d) := by
  intro i j hij
  simp only [slotRev] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> omega

/-- Copy the current word of `s`, reversed, to the end of `d`. -/
noncomputable def revw (s d : Fin t) (h : s ≠ d) : Cmd t := .prim Reverse.prim (slotRev s d) (slotRev_inj h)

theorem upd_slotRev (σ : Fin t → WTape) {s d : Fin t} (h : s ≠ d) (τ : Fin 2 → WTape) :
    upd σ (slotRev s d) τ = Function.update (Function.update σ s (τ 0)) d (τ 1) := by
  funext x
  have hi := slotRev_inj h
  by_cases hxd : x = d
  · subst hxd
    rw [Function.update_self]
    have := upd_slot σ hi τ 1
    rwa [show slotRev s x 1 = x by simp [slotRev]] at this
  · rw [Function.update_of_ne hxd]
    by_cases hxs : x = s
    · subst hxs
      rw [Function.update_self]
      have := upd_slot σ hi τ 0
      rwa [show slotRev x d 0 = x by simp [slotRev]] at this
    · rw [Function.update_of_ne hxs]
      refine upd_other σ _ τ x (fun i hi => ?_)
      simp only [slotRev] at hi; split_ifs at hi <;> simp_all

theorem runs_revw {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {L R : List (List Bool)} {w : List Bool}
    (hs : σ s = ⟨L, w :: R⟩) (hd : (σ d).right = []) :
    Runs (revw s d h) σ
      (· = Function.update (Function.update σ s ⟨w :: L, R⟩) d ⟨w.reverse :: (σ d).left, []⟩)
      (3 * w.length + 10) := by
  have hpre : Reverse.prim.pre (σ ∘ slotRev s d) :=
    ⟨by simp [slotRev, hs], by simpa [slotRev] using hd⟩
  refine ⟨_, _, Exec.prim (P := Reverse.prim) hpre, ?_, ?_⟩
  · rw [upd_slotRev σ h]
    simp [slotRev, hs, WTape.next, WTape.cur]
  · simp [slotRev, hs, WTape.cur]

end IntegerMultBounds.Schoenhage
