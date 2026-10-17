module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Descriptor tape for the CRT control scanner

The descriptor stream contains four fixed-width binary words per physical
axis. Reading a word loads it in forward order and parks its reverse on a
saved stack. After a scan, one move restores the entire descriptor stream.
The stream length is runtime data; the reader uses a fixed register bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Load one word, consuming it from `src` and saving it for restoration. -/
def crtReadWord (width tmp src saved dst spare : Fin T) : Pr P T Q A U :=
  .seq (uclear dst) (.seq (crtCpy width tmp src dst spare) (crtCMv width tmp src saved))

/-- Reading a word preserves its order on the variable register and saves its
reverse. Counter and copy scratch registers are returned empty. -/
theorem crtReadWord_runs {width tmp src saved dst spare : Fin T}
    (hreg : [width, tmp, src, saved, dst, spare].Nodup)
    (R : Regs T A) (word rest : List (Fin (A + 4))) (W : ℕ)
    (hw : (R width).length = W) (hword : word.length = W)
    (hsrc : R src = word ++ rest) (hdst : (R dst).length = W)
    (htmp : R tmp = []) (hspare : R spare = []) :
    crtRuns body (crtReadWord width tmp src saved dst spare) R
      (Function.update (Function.update (Function.update R dst word) src rest)
        saved (word.reverse ++ R saved)) (12 * W + 14) := by
  have hreg' := hreg
  regs_ne hreg'
  have s₁ := crtClear_runs (body := body) dst R
  let R₁ := Function.update R dst []
  have hR₁width : (R₁ width).length = W := by simp [R₁, ‹width ≠ dst›, hw]
  have hR₁src : R₁ src = word ++ rest := by simp [R₁, ‹src ≠ dst›, hsrc]
  have s₂ := crtCpy_runs (body := body) (c := width) (t := tmp) (src := src) (dst := dst)
    (u := spare) (by regs_nodup) R₁
    (by simp [R₁, ‹tmp ≠ dst›, htmp])
    (by simp [R₁, Ne.symm ‹dst ≠ spare›, hspare])
    (by rw [hR₁width, hR₁src, List.length_append, hword]; omega)
  have htake : (R₁ src).take (R₁ width).length ++ R₁ dst = word := by
    rw [hR₁src, hR₁width, ← hword]
    simp [R₁]
  rw [htake, hR₁width] at s₂
  let R₂ := Function.update R₁ dst word
  have hR₂width : (R₂ width).length = W := by simp [R₂, R₁, ‹width ≠ dst›, hw]
  have hR₂src : R₂ src = word ++ rest := by simp [R₂, R₁, ‹src ≠ dst›, hsrc]
  have s₃ := crtCMv_runs (body := body) (c := width) (t := tmp) (src := src) (dst := saved)
    (by regs_nodup) R₂
    (by simp [R₂, R₁, ‹tmp ≠ dst›, htmp])
    (by rw [hR₂width, hR₂src, List.length_append, hword]; omega)
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ s₃)) ?_) ?_
  · have hrest : (R₂ src).drop (R₂ width).length = rest := by
      rw [hR₂src, hR₂width, ← hword]; simp
    have htake₂ : (R₂ src).take (R₂ width).length = word := by
      rw [hR₂src, hR₂width, ← hword]; simp
    rw [hrest, htake₂]
    simp [R₂, R₁, ‹saved ≠ dst›]
  · rw [hdst, hR₂width]; omega

/-- Four binary words describing a field. -/
def crtControlWords (W : ℕ) (f : CrtControlField) : List (List (Fin (A + 4))) :=
  [binSyms W f.place, binSyms W f.bound, binSyms W f.weight,
    binSyms W (if f.active then 1 else 0)]

/-- The tape encoding of one descriptor. -/
def crtControlPacket (W : ℕ) (f : CrtControlField) : List (Fin (A + 4)) :=
  (crtControlWords W f).flatten

@[simp] lemma crtControlPacket_length (W : ℕ) (f : CrtControlField) :
    (crtControlPacket (A := A) W f).length = 4 * W := by
  simp [crtControlPacket, crtControlWords, length_binSyms]; omega

/-- Descriptor data in physical axis order, consumed by a fixed loop. -/
def crtControlTape (W : ℕ) (fs : List CrtControlField) : List (Fin (A + 4)) :=
  fs.flatMap (crtControlPacket W)

@[simp] lemma crtControlTape_length (W : ℕ) (fs : List CrtControlField) :
    (crtControlTape (A := A) W fs).length = fs.length * (4 * W) := by
  induction fs with
  | nil => simp [crtControlTape]
  | cons f fs ih =>
      simp only [crtControlTape, List.flatMap_cons, List.length_append,
        crtControlPacket_length, List.length_cons] at *
      rw [ih]; ring

/-- Restoring the saved tape after all descriptors have been consumed. -/
theorem crtControlTape_restore {src saved : Fin T} (hne : saved ≠ src)
    (W : ℕ) (fs : List CrtControlField) (R : Regs T A)
    (hsrc : R src = []) (hsaved : R saved = (crtControlTape W fs).reverse) :
    crtRuns body (crtMv saved src) R
      (Function.update (Function.update R saved []) src (crtControlTape W fs))
      (8 * fs.length * W + 2) := by
  have h := crtMv_runs (body := body) hne R
  simpa [hsaved, hsrc, crtControlTape_length, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The fixed four-field loader; its program size does not depend on axis count. -/
def crtLoadControl (width tmp src saved spare place bound weight active : Fin T) : Pr P T Q A U :=
  .seq (crtReadWord width tmp src saved place spare)
    (.seq (crtReadWord width tmp src saved bound spare)
      (.seq (crtReadWord width tmp src saved weight spare)
        (crtReadWord width tmp src saved active spare)))

/-- Loading all descriptor fields consumes exactly one packet, preserves its
reversal for restoration, and costs at most `48 W + 56` actual host steps. -/
theorem crtLoadControl_runs {width tmp src saved spare place bound weight active : Fin T}
    (hreg : [width, tmp, src, saved, spare, place, bound, weight, active].Nodup)
    (R : Regs T A) (f : CrtControlField) (rest : List (Fin (A + 4))) (W : ℕ)
    (hw : (R width).length = W)
    (hsrc : R src = crtControlPacket W f ++ rest)
    (hp : (R place).length = W) (hb : (R bound).length = W)
    (hk : (R weight).length = W) (ha : (R active).length = W)
    (htmp : R tmp = []) (hspare : R spare = []) :
    crtRuns body (crtLoadControl width tmp src saved spare place bound weight active) R
      (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update R
          place (binSyms W f.place)) bound (binSyms W f.bound))
          weight (binSyms W f.weight)) active (binSyms W (if f.active then 1 else 0)))
          src rest) saved ((crtControlPacket W f).reverse ++ R saved))
      (48 * W + 56) := by
  have hreg' := hreg
  regs_ne hreg'
  let p : List (Fin (A + 4)) := binSyms W f.place
  let b : List (Fin (A + 4)) := binSyms W f.bound
  let k : List (Fin (A + 4)) := binSyms W f.weight
  let a : List (Fin (A + 4)) := binSyms W (if f.active then 1 else 0)
  have hsrc' : R src = p ++ (b ++ (k ++ (a ++ rest))) := by
    simpa [crtControlPacket, crtControlWords, p, b, k, a, List.append_assoc] using hsrc
  let R₁ := Function.update (Function.update (Function.update R place p)
    src (b ++ (k ++ (a ++ rest)))) saved (p.reverse ++ R saved)
  let R₂ := Function.update (Function.update (Function.update R₁ bound b)
    src (k ++ (a ++ rest))) saved (b.reverse ++ R₁ saved)
  let R₃ := Function.update (Function.update (Function.update R₂ weight k)
    src (a ++ rest)) saved (k.reverse ++ R₂ saved)
  have h₁ : crtRuns body (crtReadWord width tmp src saved place spare) R R₁ (12*W+14) :=
    crtReadWord_runs (by regs_nodup) R p _ W hw (by simp [p, length_binSyms]) hsrc' hp htmp hspare
  have h₂ : crtRuns body (crtReadWord width tmp src saved bound spare) R₁ R₂ (12*W+14) := by
    apply crtReadWord_runs (by regs_nodup) R₁ b (k ++ (a ++ rest)) W
    all_goals simp_all [eq_comm, R₁, b, length_binSyms]
  have h₃ : crtRuns body (crtReadWord width tmp src saved weight spare) R₂ R₃ (12*W+14) := by
    apply crtReadWord_runs (by regs_nodup) R₂ k (a ++ rest) W
    all_goals simp_all [eq_comm, R₁, R₂, k, length_binSyms]
  have h₄ := crtReadWord_runs (body := body) (width := width) (tmp := tmp)
    (src := src) (saved := saved) (dst := active) (spare := spare)
    (by regs_nodup) R₃ a rest W
    (by simp_all [eq_comm, R₃, R₂, R₁]) (by simp [a, length_binSyms])
    (by simp_all [eq_comm, R₃]) (by simp_all [eq_comm, R₃, R₂, R₁])
    (by simp_all [eq_comm, R₃, R₂, R₁]) (by simp_all [eq_comm, R₃, R₂, R₁])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))) ?_) (by omega)
  clear hsrc hsrc' h₁ h₂ h₃ h₄
  ext j
  simp only [R₃, R₂, R₁, p, b, k, a, crtControlPacket, crtControlWords,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.reverse_append,
    Function.update_apply]
  split_ifs <;> simp_all [List.append_assoc]

/-- Positive width makes the tape emptiness test a descriptor-list test. -/
@[simp] theorem crtControlTape_eq_nil (W : ℕ) (hW : 0 < W)
    (fs : List CrtControlField) :
    crtControlTape (A := A) W fs = [] ↔ fs = [] := by
  rw [← List.length_eq_zero_iff, crtControlTape_length]
  simp [Nat.ne_of_gt hW]

/-- Descriptor variables are reset between packets; the loop keeps only its
address, weighted sum and validity flag live. -/
def crtControlConsume : TblCode 10 :=
  .seq crtControlStep (tblBlock 10 [.zero 1, .zero 2, .zero 3] (.zero 4))

def crtControlConsumeState {A : ℕ} (w : ℕ) (st : TblSt 10 A) : TblSt 10 A :=
  tblExactList A w [.zero 1, .zero 2, .zero 3, .zero 4] (crtControlStepState w st)

/-- Cleaning the descriptor fields adds four atoms to the nine-atom step. -/
theorem crtControlConsume_do {A W w : ℕ} (st : TblSt 10 A)
    (hfit : st.val 9 < st.val 4 →
      st.val 5 + st.val 0 / st.val 1 * st.val 3 < 2 ^ W) :
    TblDo A W w crtControlConsume st
      (fun t => t = crtControlConsumeState w st) 13 := by
  unfold crtControlConsume
  refine (crtControlStep_do (w := w) st hfit).seq (K₂ := 4) ?_
  intro t ht
  subst t
  apply TblDo.block [.zero 1, .zero 2, .zero 3] (.zero 4)
  · simp [tblFitsList, TblIns.fits]
  · rfl

/-- Cleanup preserves the arithmetic result and accumulator while returning
all four descriptor registers to zero. -/
theorem crtControlConsumeState_spec {A : ℕ} (w : ℕ) (st : TblSt 10 A) :
    let t := crtControlConsumeState w st
    t.val 1 = 0 ∧ t.val 2 = 0 ∧ t.val 3 = 0 ∧ t.val 4 = 0 ∧
    (∀ j, j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 4 →
      t.val j = (crtControlStepState w st).val j) ∧ t.acc = st.acc := by
  have hs := crtControlStepState_spec w st
  simp only [crtControlConsumeState, tblExactList, TblIns.exact]
  refine ⟨rfl, rfl, rfl, rfl, ?_, hs.2.2.2.2.2.2⟩
  intro j h1 h2 h3 h4
  simp [h1, h2, h3, h4]

end IntegerMultBounds.MathlibTM2.Fast
