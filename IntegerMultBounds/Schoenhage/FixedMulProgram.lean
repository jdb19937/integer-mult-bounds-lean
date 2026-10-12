module

public import IntegerMultBounds.Schoenhage.FixedMulWords
public import IntegerMultBounds.Schoenhage.RingPointwiseProgram

/-! The word-level fixed-point multiply `fixedMulW` as a literal 91-tape
program on raw bit strings: the operands on `zF`, `zG` and the rulers on
`iP`, `iW` are sealed into words, the compiled word program runs, and every
word is unsealed again, leaving `FixedMul.result x y p w` on `zO`
(`fmProg_hoare`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- The word tapes at the start. -/
def fmStart (x y : List Bool) (p w : ℕ) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update (Function.update (fun _ => emp)
    zF (reg x)) zG (reg y)) iP (reg (ones p))) iW (reg (ones w))

/-- The raw bank: operands, rulers and output as bit strings from cell zero, all else blank. -/
def rawFM (x y : List Bool) (p w : ℕ) (out : List Bool) : Tapes 𝕌 0 :=
  ⟨fun _ => 0, fun i => if i = zF then wordAt x else if i = zG then wordAt y else if i = iP then wordAt (ones p)
    else if i = iW then wordAt (ones w) else if i = zO then wordAt out else fun _ => blank⟩

theorem enc_fmStart (x y : List Bool) (p w : ℕ) (out : Option (List Bool)) :
    enc (a := 0) (match out with | none => fmStart x y p w | some o => Function.update (fmStart x y p w) zO (reg o)) =
      ⟨fun _ => 0, fun i => if i = zF then (⟨[], [x]⟩ : WTape).tape else if i = zG then (⟨[], [y]⟩ : WTape).tape
        else if i = iP then (⟨[], [ones p]⟩ : WTape).tape else if i = iW then (⟨[], [ones w]⟩ : WTape).tape
        else if i = zO then (match out with | none => fun _ => blank | some o => (⟨[], [o]⟩ : WTape).tape)
        else fun _ => blank⟩ := by
  cases out <;>
  · simp only [enc]
    congr 1
    · funext i; simp only [fmStart, Function.update_apply]; split_ifs <;> rfl
    · funext i; simp only [fmStart, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> first | rfl | exact emp_tape | (tsimp at *)

/-- The compiled word program. -/
noncomputable def fmCoreProg : Program 𝕌 (compile (a := 0) (by decide) fixedMulW).1 0 :=
  (compile (a := 0) (by decide) fixedMulW).2

theorem fmCoreProg_hoare {x y : List Bool} {p w : ℕ} (hx : x.length = w) (hy : y.length = w) (hw : 1 ≤ w)
    (hpw : p ≤ w) :
    HoareTime fmCoreProg (· = enc (fmStart x y p w))
      (· = enc (Function.update (fmStart x y p w) zO (reg (FixedMul.result x y p w)))) (fixedMulWCost w x y) := by
  have e : ∀ s : Fin 𝕌, s ≠ zF → s ≠ zG → s ≠ iP → s ≠ iW → fmStart x y p w s = emp := by
    intro s h1 h2 h3 h4
    simp [fmStart, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]
  have hc : Clean (fmStart x y p w) := by
    funext i
    exact e _ (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
  obtain ⟨σ', k, hex, hq, hk⟩ := runs_fixedMulW hx hy hw hpw (fmStart x y p w) hc
    (by tsimp [fmStart]) (by tsimp [fmStart]) (by tsimp [fmStart]) (by tsimp [fmStart])
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide))
  subst hq
  exact (compile_correct (by decide) hex).consequence (fun _ h => h) (fun _ h => h) hk

/-- Seal the inputs, run the core, unseal. -/
noncomputable def fmProg :=
  Machine.seq (sealAt (a := 0) zF) <| Machine.seq (sealAt (a := 0) zG) <| Machine.seq (sealAt (a := 0) iP) <|
  Machine.seq (sealAt (a := 0) iW) <| Machine.seq fmCoreProg <| Machine.seq (unsealAt (a := 0) zO) <|
  Machine.seq (unsealAt (a := 0) zF) <| Machine.seq (unsealAt (a := 0) zG) <|
  Machine.seq (unsealAt (a := 0) iP) (unsealAt (a := 0) iW)

set_option maxHeartbeats 4000000 in
theorem fmProg_hoare {x y : List Bool} {p w : ℕ} (hx : x.length = w) (hy : y.length = w) (hw : 1 ≤ w)
    (hpw : p ≤ w) :
    HoareTime fmProg (· = rawFM x y p w []) (· = rawFM x y p w (FixedMul.result x y p w))
      (fixedMulWCost w x y + 20 * w + 200) := by
  set out := FixedMul.result x y p w
  have hol : out.length = w := by
    unfold out FixedMul.result; split_ifs <;> simp [TwosComplement.negWord_length, Gather.field]
  set v0 := rawFM x y p w []
  have h1 := sealAt_hoare (a := 0) zF x v0 rfl (by simp [v0, rawFM])
  set v1 : Tapes 𝕌 0 := ⟨v0.head, Function.update v0.tape zF (⟨[], [x]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := 0) zG y v1 rfl (by tsimp [v1, v0, rawFM])
  set v2 : Tapes 𝕌 0 := ⟨v1.head, Function.update v1.tape zG (⟨[], [y]⟩ : WTape).tape⟩
  have h3 := sealAt_hoare (a := 0) iP (ones p) v2 rfl (by tsimp [v2, v1, v0, rawFM])
  set v3 : Tapes 𝕌 0 := ⟨v2.head, Function.update v2.tape iP (⟨[], [ones p]⟩ : WTape).tape⟩
  have h4 := sealAt_hoare (a := 0) iW (ones w) v3 rfl (by tsimp [v3, v2, v1, v0, rawFM])
  have e4 : (⟨v3.head, Function.update v3.tape iW (⟨[], [ones w]⟩ : WTape).tape⟩ : Tapes 𝕌 0) =
      enc (fmStart x y p w) := by
    rw [enc_fmStart x y p w none]
    simp only [v3, v2, v1, v0, rawFM, Tapes.mk.injEq, true_and]
    funext i; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | exact wordAt_nil | (tsimp at *)
  have h5 := fmCoreProg_hoare hx hy hw hpw
  set u0 := enc (a := 0) (Function.update (fmStart x y p w) zO (reg out))
  have hu : u0 = _ := enc_fmStart x y p w (some out)
  have h6 := unsealAt_hoare (a := 0) zO out u0 (by rw [hu]) (by rw [hu]; tsimp)
  set u1 : Tapes 𝕌 0 := ⟨u0.head, Function.update u0.tape zO (wordAt out)⟩
  have h7 := unsealAt_hoare (a := 0) zF x u1 (by simp only [u1]; rw [hu]) (by simp only [u1]; rw [hu]; tsimp)
  set u2 : Tapes 𝕌 0 := ⟨u1.head, Function.update u1.tape zF (wordAt x)⟩
  have h8 := unsealAt_hoare (a := 0) zG y u2 (by simp only [u2, u1]; rw [hu])
    (by simp only [u2, u1]; rw [hu]; tsimp)
  set u3 : Tapes 𝕌 0 := ⟨u2.head, Function.update u2.tape zG (wordAt y)⟩
  have h9 := unsealAt_hoare (a := 0) iP (ones p) u3 (by simp only [u3, u2, u1]; rw [hu])
    (by simp only [u3, u2, u1]; rw [hu]; tsimp)
  set u4 : Tapes 𝕌 0 := ⟨u3.head, Function.update u3.tape iP (wordAt (ones p))⟩
  have h10 := unsealAt_hoare (a := 0) iW (ones w) u4 (by simp only [u4, u3, u2, u1]; rw [hu])
    (by simp only [u4, u3, u2, u1]; rw [hu]; tsimp)
  have e10 : (⟨u4.head, Function.update u4.tape iW (wordAt (ones w))⟩ : Tapes 𝕌 0) = rawFM x y p w out := by
    simp only [u4, u3, u2, u1, rawFM, Tapes.mk.injEq]
    rw [hu]
    refine ⟨rfl, ?_⟩
    funext i; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | (tsimp at *)
  refine ((h1.seq (h2.seq (h3.seq (h4.seq ((h5.consequence (fun v h => h.trans e4) (fun v h => h) le_rfl).seq
    (h6.seq (h7.seq (h8.seq (h9.seq h10)))))))))).consequence (fun v h => h) (fun v h => h.trans e10) ?_
  simp only [length_ones, hol, hx, hy]
  omega

/-! ### Runtime -/

/-- The multiply's runtime at width `w`: `O(w log w log log w)`. -/
noncomputable def fmTime (w : ℕ) : ℕ :=
  costC cA cB cC0 * (8 * w + 1) * (bitlen (8 * w) + 1) * (3 * bitlen (bitlen (8 * w)) + 1) + 8000 * w + 80000

theorem fmCost_le {x y : List Bool} {w : ℕ} (hx : x.length = w) (hy : y.length = w) (hw : 1 ≤ w) :
    fixedMulWCost w x y + 20 * w + 200 ≤ fmTime w := by
  have h1 := ssCost_le (topN (2 * w)) (bval (FixedMul.mag x)) (bval (FixedMul.mag y))
  have h2 := cost_topN cA cB cC0 (m := 2 * w) (by omega)
  have h3 := (topN_facts (m := 2 * w) (by omega)).2.1
  rw [show 4 * (2 * w) = 8 * w by ring] at h2 h3
  unfold fmTime fixedMulWCost exCost
  rw [FixedMul.mag_length, FixedMul.mag_length, hx, hy]
  omega

/-- `fmProg` within `fmTime w`. -/
theorem fmProg_time {x y : List Bool} {p w : ℕ} (hx : x.length = w) (hy : y.length = w) (hw : 1 ≤ w)
    (hpw : p ≤ w) :
    HoareTime fmProg (· = rawFM x y p w []) (· = rawFM x y p w (FixedMul.result x y p w)) (fmTime w) :=
  (fmProg_hoare hx hy hw hpw).consequence (fun _ h => h) (fun _ h => h) (fmCost_le hx hy hw)

end IntegerMultBounds.Schoenhage
