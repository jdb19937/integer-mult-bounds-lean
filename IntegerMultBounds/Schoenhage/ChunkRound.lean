module

public import IntegerMultBounds.Schoenhage.ConvPrims
public import IntegerMultBounds.Schoenhage.PrefixRoundRun
public import IntegerMultBounds.Spec.SimultaneousLayerFacts

/-! §6 task 4, the chunk-group rounds. In the paper's layout the computed round of
chunk slot `b + cK + ρ` is the round's twist of the simultaneous layer's output
`Q_p(ℋ z)` on `[P] × [2^K]^D × [2^(cDK)]` with offset `ρ` (`chunk_round_eq`). A
program meeting `prop:simultaneous-layer` runs between word tapes with the layer
header on tape 0 and the array on tape 1, replaced in place (`prog1_hoare`,
`layer_call`); the twist is `runs_slotTwist`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct NLogN

variable {t q a : ℕ}

/-! ### The computed round -/

/-- `chunk_round_eq`: on the records of the array, the computed chunk-group round is the twist of
the layer's output. -/
theorem chunk_round_eq {r : ℕ} [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {c ρ : ℕ}
    (hc : c < (ℓ - 1) / K) (hρ : ρ < K) (p M : ℕ) (zs : List (Rec r)) {x : ℕ} (hx : x < M) :
    roundArr p (slotRound (paperPerm hL) ts ((ℓ - 1) % K + c * K + ρ) (arrayVec p zs)) x =
      twist (slotExp (paperPerm hL) r ts (slotAxes ts ((ℓ - 1) % K + c * K + ρ)) ((ℓ - 1) % K + c * K + ρ))
        (arrayVec p (layerOut p ts.length K ρ (2 ^ (c * ts.length * K)) M zs)) x := by
  rw [paper_slotRound_chunk hL hc hρ, roundArr_twist]
  simp only [twist]
  congr 1
  rw [arrayVec_layerOut zs hx]
  rfl

/-! ### A layer program on word tapes -/

/-- Tape `j` of a bank with at least two tapes. -/
def tq (ht : 2 ≤ t) (j : ℕ) (hj : j < 2) : Fin t := ⟨j, by omega⟩

/-- Unseal tapes 0 and 1, run `M`, seal them again. -/
noncomputable def prog1 (M : Program t q a) (ht : 2 ≤ t) :=
  Machine.seq (unsealAt (tq ht 0 (by decide))) <| Machine.seq (unsealAt (tq ht 1 (by decide))) <|
  Machine.seq M <| Machine.seq (sealAt (tq ht 0 (by decide))) (sealAt (tq ht 1 (by decide)))

/-- Header and array as words on tapes 0 and 1, every other tape empty. -/
def start1 (t : ℕ) (hdr A : List Bool) : Fin t → WTape :=
  fun i => if i.val = 0 then reg hdr else if i.val = 1 then reg A else emp

set_option maxHeartbeats 4000000 in
theorem prog1_hoare (M : Program t q a) (ht : 2 ≤ t) {hdr A A' : List Bool} {k : ℕ}
    (hM : HoareTime M (· = bank hdr A [] []) (· = bank hdr A' [] []) k) :
    HoareTime (prog1 M ht) (· = enc (start1 t hdr A)) (· = enc (start1 t hdr A'))
      (k + 4 * (hdr.length + A.length + A'.length) + 40) := by
  have v0 : (tq ht 0 (by decide)).val = 0 := rfl
  have v1 : (tq ht 1 (by decide)).val = 1 := rfl
  have n10 : tq ht 1 (by decide) ≠ tq ht 0 (by decide) := Fin.ne_of_val_ne (by rw [v0, v1]; decide)
  set u0 := enc (a := a) (start1 t hdr A)
  have hh0 : u0.head = fun _ => 0 := by
    funext x; simp only [u0, enc, start1]; split_ifs <;> rfl
  have h1 := unsealAt_hoare (a := a) (tq ht 0 (by decide)) hdr u0 (by rw [hh0])
    (by simp [u0, enc, start1, v0, reg])
  set u1 : Tapes t a := ⟨u0.head, Function.update u0.tape (tq ht 0 (by decide)) (wordAt hdr)⟩
  have h2 := unsealAt_hoare (a := a) (tq ht 1 (by decide)) A u1 (by simp [u1, hh0])
    (by simp [u1, u0, enc, start1, v1, reg, Function.update_of_ne n10])
  have e2 : (⟨u1.head, Function.update u1.tape (tq ht 1 (by decide)) (wordAt A)⟩ : Tapes t a) =
      bank hdr A [] [] := by
    simp only [u1, bank, hh0, Tapes.mk.injEq, true_and]
    funext i
    simp only [Function.update_apply, u0, enc, start1, Fin.ext_iff, v0, v1]
    split_ifs <;> first | rfl | omega | simp [emp_tape']
  set u3 := bank (t := t) (a := a) hdr A' [] []
  have h4 := sealAt_hoare (a := a) (tq ht 0 (by decide)) hdr u3 rfl (by simp [u3, bank, v0])
  set u4 : Tapes t a := ⟨u3.head, Function.update u3.tape (tq ht 0 (by decide)) (⟨[], [hdr]⟩ : WTape).tape⟩
  have h5 := sealAt_hoare (a := a) (tq ht 1 (by decide)) A' u4 rfl
    (by simp [u4, u3, bank, v1, Function.update_of_ne n10])
  have e5 : (⟨u4.head, Function.update u4.tape (tq ht 1 (by decide)) (⟨[], [A']⟩ : WTape).tape⟩ : Tapes t a) =
      enc (start1 t hdr A') := by
    simp only [u4, u3, bank, enc, Tapes.mk.injEq]
    constructor
    · funext x
      simp only [start1]
      split_ifs <;> rfl
    · funext i
      simp only [Function.update_apply, start1, Fin.ext_iff, v0, v1]
      split_ifs <;> first | rfl | omega | simp [emp_tape']
  refine (h1.seq (h2.seq ((hM.consequence (fun v h => h.trans e2) (fun v h => h) le_rfl).seq
    (h4.seq h5)))).consequence (fun v h => h) (fun v h => h.trans e5) ?_
  omega

/-- One layer call: a program meeting `prop:simultaneous-layer` for the call replaces the array word by
the layer's output, as a contract between word banks, within the layer's cost and the data movement. -/
theorem layer_call {LP : LayerParams} {M : Program t q a} (ht : 2 ≤ t) {C : ℝ}
    {p d r D Pa S K ρ w : ℕ} (hM : MeetsLayer LP M C p d r D Pa S K ρ w)
    (zs : List (Rec r)) (hzl : zs.length = Pa * S * 2 ^ (K * D)) (hz : ∀ z ∈ zs, DiskGrid p z.1 z.2) :
    ∃ k : ℕ, (k : ℝ) ≤ C * layerCost LP d r (Pa * S * 2 ^ (K * D)) w +
        4 * ((layerHeader p d r D Pa S K ρ w).length + 2 * (2 * r * w * zs.length)) + 40 ∧
      HoareTo (prog1 M ht) (start1 t (layerHeader p d r D Pa S K ρ w) (array w zs))
        (start1 t (layerHeader p d r D Pa S K ρ w) (array w (layerOut p D K ρ S (Pa * S * 2 ^ (K * D)) zs))) k := by
  obtain ⟨k, hk, hH⟩ := hM zs hzl hz
  refine ⟨_, ?_, prog1_hoare M ht hH⟩
  have hl1 : (array w zs).length = 2 * r * w * zs.length := length_array w zs
  have hl2 : (array w (layerOut p D K ρ S (Pa * S * 2 ^ (K * D)) zs)).length = 2 * r * w * zs.length := by
    rw [length_array]; simp [layerOut, hzl]
  rw [hl1, hl2]
  push_cast
  linarith

end IntegerMultBounds.Schoenhage
