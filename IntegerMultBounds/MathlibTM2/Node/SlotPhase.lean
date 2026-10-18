module

public import IntegerMultBounds.MathlibTM2.Node.Body

/-!
# Masked phase passes on one wire

`signPass b` multiplies the wire `inl b` by `i ^ (2 · popcount(mask ∧ a))`, `mask` being the
strided mask of the terminal vector of `b`. The same three steps (build a strided mask, run the
phase program, clear the mask) work for any slot vector, any wire and any `c : ZMod 4`.

* `vecPred u`: the slots selected by a vector `u : Fin m → ZMod 2`; `tvPred b = vecPred
  (terminalVector b)`.
* `addrBits_maskVal_vec`: the strided mask of `vecPred u` is the sign mask of `u` on the active
  bits.
* `maskPass pred c fw` and `maskPass_exec`: wire `fw` goes from the stream of `Z` to the stream
  of `phaseZ mask c Z`.
* `slotPhase x c fw` and `slotPhase_exec`: the pass for `u = e_x`, which multiplies every cell by
  `i ^ (c · Σ_columns a_x)`, the slot phase `i ^ (c x_x)` (T16's `MPrim.phase x c`) applied in
  every active column.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg

/-- The slots selected by a vector of slot bits. -/
noncomputable def vecPred (u : Fin m → ZMod 2) (s : ℕ) : Bool :=
  if h : s < m then decide (u ⟨s, h⟩ = 1) else false

theorem tvPred_eq_vecPred (b : Wires.Address 25) :
    tvPred b = vecPred (ComplexEndpoints.terminalVector b) := rfl

/-- The strided mask of `vecPred u` is the sign mask of `u` on the active bits. -/
lemma addrBits_maskVal_vec {a₀ ρ K k n : ℕ} (hK : 1 ≤ K) (hfit : ∀ i < m * k, a₀ + ρ + K * i < n)
    (u : Fin m → ZMod 2) :
    addrBits n (maskVal (a₀ + ρ) K k m (vecPred u)) =
      signMask (actMap a₀ ρ K (m * k) n hfit) u := by
  funext t
  have key : (maskVal (a₀ + ρ) K k m (vecPred u)).testBit t = true ↔
      ∃ (j : Fin m) (c : Fin k), actMap a₀ ρ K (m * k) n hfit (bitIdx j c) = t ∧ u j = 1 := by
    rw [testBit_maskVal hK]
    constructor
    · rintro ⟨i, hi, hp, ht⟩
      have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hi
      have hj : i / k < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
      refine ⟨⟨i / k, hj⟩, ⟨i % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
      · apply Fin.ext
        simp only [actMap, bitIdx, finProdFinEquiv, Equiv.coe_fn_mk]
        rw [ht, Nat.mod_add_div]
      · simpa [vecPred, hj] using hp
    · rintro ⟨j, c, he, hj⟩
      have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; exact Fin.elim0 c
      refine ⟨c + k * j, (bitIdx j c).2, ?_, ?_⟩
      · have hd : (c.val + k * j.val) / k = j.val := by
          rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt c.2, Nat.zero_add]
        simp [vecPred, hd, j.2, hj]
      · rw [← he]
        rfl
  simp only [addrBits, signMask]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

section MaskPass

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- One masked phase pass on wire `fw`: build the strided mask of `pred` on `ph .msk`, run the
phase pass with constant `c` on the wire, and clear the mask. -/
noncomputable def maskPass (pred : ℕ → Bool) (c : ZMod 4) (fw : NWire) : Pr P (nT BReg) Q A U :=
  .seq (strideMask (reg .n) (reg (.sc 0)) (reg .K) (reg (.sc 1)) (reg (.ph .msk)) (reg (.sc 2))
      (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5)) m pred)
    (.seq (phaseProg (phMap (reg (.wire fw))) (reg .st) c) (uclear (reg (.ph .msk))))

theorem signPass_eq_maskPass (b : Wires.Address 25) :
    signPass (BReg := BReg) (Q := Q) (A := A) (U := U) (P := P) b =
      maskPass (tvPred b) 2 (.inl b) := rfl

/-- **One masked phase pass.** Wire `fw` holding the stream of `Z` ends holding the stream of
`phaseZ mask c Z`, `mask` being the strided mask of `pred`; every other register ends as it
started. -/
theorem maskPass_exec (hA : 5 ≤ A) {n o K k R r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K)
    (pred : ℕ → Bool) (c : ZMod 4) (fw : NWire) (mask : Fin n → ZMod 2)
    (hmask : addrBits n (maskVal o K k m pred) = mask) (Z : ZArr (Fin R × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hG : SignGood S.R n o K k R r w)
    (hX : S.R (reg (.wire fw)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ signCost n o K k R r w ∧
      Exec body (maskPass pred c fw) (mk v S) steps (mk v' { S with
        R := Function.update S.R (reg (.wire fw)) (encZ A w (phaseZ mask c Z)) }) := by
  have hmsk : S.R (reg (.ph .msk)) = [] := hG.hph .msk (by decide) (by decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := strideMask_exec body
    (nodup_map_reg (l := [.n, .sc 0, .K, .sc 1, .ph .msk, .sc 2, .sc 3, .sc 4, .sc 5]) (by simp))
    m pred v S hG.hn hG.ho hG.hK hG.hk hK (hG.hsc 2 (by decide)) (hG.hsc 3 (by decide))
    (hG.hsc 4 (by decide)) (hG.hsc 5 (by decide))
  obtain ⟨R₁, he₁, hR₁b, hR₁⟩ := exec_upd body (S := S) (R := S.R) he₁
  have hph : ∀ x, x ≠ PhaseReg.arr → phMap (reg (BReg := BReg) (.wire fw)) x =
      reg (.ph x) := fun x hx => phMap_of_ne _ hx
  have hR₁ph : ∀ x, x ≠ .msk → R₁ (reg (.ph x)) = S.R (reg (.ph x)) :=
    fun x hx => hR₁ _ (reg_ne (by simpa using hx))
  have hP : ∀ x, x ≠ PhaseReg.arr → x ≠ .msk →
      R₁ (phMap (reg (.wire fw)) x) = S.R (reg (.ph x)) :=
    fun x h1 h2 => by rw [hph x h1, hR₁ph x h2]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := phaseProg_exec body
    (ρ := phMap (reg (.wire fw))) (st := reg .st)
    (phMap_injective (fun x => reg_ne (by simp)))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hph _ (by decide)]; exact reg_ne (by simp)))
    hA hr hw c mask (maskVal o K k m pred) hmask Z
    (cs := S.R (reg (.ph .rc))) (ws := S.R (reg (.ph .wc))) (kk := S.R (reg (.ph .cnt)))
    (hG.hph .rc (by decide) (by decide)) (hG.hph .wc (by decide) (by decide)) hG.hcnt v₁
    { S with R := R₁ }
    (by dsimp only; rw [phMap_arr, hR₁ _ (reg_ne (by simp)), hX])
    (fun q => by
      dsimp only; rw [hP _ (by simp) (by simp)]; exact hG.hph (.cls q) (by simp) (by simp))
    (hP _ (by decide) (by decide)) (hP _ (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .tmp (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .aux (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .aux2 (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .af (by decide) (by decide))
    (by dsimp only; rw [hph _ (by decide), hR₁b, hmsk, List.append_nil])
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .t0 (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .t1 (by decide) (by decide))
    (hP _ (by decide) (by decide))
  obtain ⟨R₂, he₂, hR₂b, hR₂⟩ := exec_upd body (S := S) (R := R₁) he₂
  rw [phMap_arr] at hR₂b hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (reg (.ph .msk)) v₂ { S with R := R₂ }
  obtain ⟨R₃, he₃, hR₃b, hR₃⟩ := exec_upd body (S := S) (R := R₂) he₃
  have hR₂m : R₂ (reg (.ph .msk)) = binSyms n (maskVal o K k m pred) := by
    rw [hR₂ _ (reg_ne (by simp)), hR₁b, hmsk, List.append_nil]
  have hfin : R₃ = Function.update S.R (reg (.wire fw)) (encZ A w (phaseZ mask c Z)) := by
    funext x
    by_cases h1 : x = reg (.wire fw)
    · rw [h1, Function.update_self, hR₃ _ (reg_ne (by simp)), hR₂b]
    rw [Function.update_of_ne h1]
    by_cases h2 : x = reg (.ph .msk)
    · rw [h2, hR₃b, hmsk]
    rw [hR₃ x h2, hR₂ x h1, hR₁ x h2]
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl
    (by rw [hfin])⟩
  dsimp only
  rw [hR₂m, length_binSyms]
  unfold signCost
  omega

/-- The slot phase `i ^ (c x_x)` in every active column of wire `fw`. -/
noncomputable def slotPhase (x : Fin m) (c : ZMod 4) (fw : NWire) : Pr P (nT BReg) Q A U :=
  maskPass (vecPred (Pi.single x 1)) c fw

/-- **The slot phase.** Wire `fw` goes from the stream of `Z` to the stream of
`phaseZ (signMask e (e_x)) c Z`, the phase `i ^ (c · Σ_columns a_x)`; every other register ends
as it started. -/
theorem slotPhase_exec (hA : 5 ≤ A) {a₀ ρ n K k R r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hK : 1 ≤ K) (hfit : ∀ i < m * k, a₀ + ρ + K * i < n) (x : Fin m) (c : ZMod 4) (fw : NWire)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hG : SignGood S.R n (a₀ + ρ) K k R r w) (hX : S.R (reg (.wire fw)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ signCost n (a₀ + ρ) K k R r w ∧
      Exec body (slotPhase x c fw) (mk v S) steps (mk v' { S with
        R := Function.update S.R (reg (.wire fw))
          (encZ A w (phaseZ (signMask (actMap a₀ ρ K (m * k) n hfit) (Pi.single x 1)) c Z)) }) :=
  maskPass_exec body hA hr hw hK _ c fw _ (addrBits_maskVal_vec hK hfit _) Z v S hG hX

end MaskPass

end IntegerMultBounds.MathlibTM2.LayerMachine
