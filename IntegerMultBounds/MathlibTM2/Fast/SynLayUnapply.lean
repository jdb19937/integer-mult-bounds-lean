module

public import IntegerMultBounds.MathlibTM2.Fast.SynLayKit

/-!
# The restoring layout machine on description streams

Paper §6, proof of `lem:synthetic-transform-cost`. The counterpart of `ldLayStage_exec`
(`Fast/LoadLayout.lean`) for the restoring machine `layUnapply` (`Fast/Layout.lean`): from a
base file (`LdlBase`) holding the description streams of the exchanges `xs` and then of the
single-bit moves `bs`, the machine with the loaders `ldlPrepM`, `ldlPrepX` moves the stream by
`xs` and then `bs`.

* `ldlWU`: the register files of the restoring machine, the exchange phase first (`ldlWX`),
  then the bit phase (`ldlWM`) from the file after the last exchange.
* `sly_unstage_gen`: the run for any `xs`, `bs`; `sly_unstage_exec`: for the inverse layout
  `(layXcs es ℓ K B).reverse`, `((layBits es ℓ K).map Prod.swap).reverse`, which leaves
  `(moveRecs (layRec (layPerm es ℓ K)).symm l).flatten` on `str`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Files

variable {T A t₀ : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

/-- The register files of the restoring machine: `ldlWX` up to `|xs|`, then `ldlWM`. -/
noncomputable def ldlWU (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (xs : List LayXcD) (bs : List (ℕ × ℕ)) (i : ℕ) :
    Fin T → List (Fin (A + 4)) :=
  if i ≤ xs.length then ldlWX rg lr hd A w R₀ xs i
  else ldlWM rg lr A n (ldlWX rg lr hd A w R₀ xs xs.length) bs (i - xs.length)

theorem ldlWU_X (hd : Fin 5 → Fin t₀) (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4)))
    (xs : List LayXcD) (bs : List (ℕ × ℕ)) {j : ℕ} (hj : j ≤ xs.length) :
    ldlWU rg lr hd A n w R₀ xs bs j = ldlWX rg lr hd A w R₀ xs j := by
  rw [ldlWU, if_pos hj]

theorem ldlWU_M (hd : Fin 5 → Fin t₀) (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4)))
    (xs : List LayXcD) (bs : List (ℕ × ℕ)) (j : ℕ) :
    ldlWU rg lr hd A n w R₀ xs bs (xs.length + j) =
      ldlWM rg lr A n (ldlWX rg lr hd A w R₀ xs xs.length) bs j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [ldlWU, ldlWM]
  · rw [ldlWU, if_neg (by omega), Nat.add_sub_cancel_left]

end Files

section Stage

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

/-- **The restoring machine on description streams.** From a base file holding the streams
of the exchanges `xs` and the single-bit moves `bs`, `layUnapply` with the loaders `ldlPrepM`,
`ldlPrepX` moves the stream of `2^n` records by `xs` and then `bs`; the files follow `ldlWU`. -/
theorem sly_unstage_gen (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (h : LdlRegs rg lr)
    (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka) (hpay : ∀ k, hd k ≠ pay) {n K B wX : ℕ}
    (hB : 1 ≤ B) (xs : List LayXcD) (bs : List (ℕ × ℕ)) (hxs : ∀ d ∈ xs, d.OK n K B)
    (hbs : ∀ e ∈ bs, e.1 < n ∧ e.2 < n) (hwX : ∀ d ∈ xs, ∀ k, (d.hs k).length ≤ wX)
    (R₀ : Fin T → List (Fin (prime + Ka + 4))) (hb : LdlBase rg lr hd pay R₀ n B wX bs xs)
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = bs.length)
    (hcsX : csX.length = xs.length) :
    LayRuns body (layUnapply hd pay hi hQ rg (fun _ _ e => by simpa using h.rg_inj e) hT
        (ldlPrepM rg lr) (ldlPrepX hd rg lr))
      (layDyn rg R₀ l.flatten csM [] csX [])
      (layDyn rg (ldlWU rg lr hd (prime + Ka) n wX R₀ xs bs (xs.length + bs.length))
        (layStream K n (xs.map LayXcD.move ++ layBitMoves bs) l).flatten csM [] csX [])
      (layXcLoopCost T t₀ n K B rg (ldlWU rg lr hd (prime + Ka) n wX R₀ xs bs)
          (fun _ => 60 * wX + 75) xs +
        layBitCost n B (fun _ => 14 * n + 12) bs.length) := by
  set W := ldlWU rg lr hd (prime + Ka) n wX R₀ xs bs with hW
  set R₁ := ldlWX rg lr hd (prime + Ka) wX R₀ xs xs.length with hR₁
  have hW0 : W 0 = R₀ := by rw [hW, ldlWU_X _ _ _ _ _ _ _ (Nat.zero_le _)]; rfl
  have hHne : ∀ k (x : LayReg t₀), (∀ i, x ≠ .sw i) → ldlH rg hd k ≠ rg x := by
    intro k x hx e
    exact hx _ (h.rg_inj e).symm
  have hHk : ∀ k (i : Fin t₀), hd k ≠ i → ldlH rg hd k ≠ rg (.sw (reg i)) := by
    intro k i hki e
    have e1 := h.rg_inj e
    simp only [LayReg.sw.injEq] at e1
    exact hki (BinaryInterchangeRun.slot_injective e1)
  have hR₁rg : ∀ x : LayReg t₀, (∀ i, x ≠ .sw i) → R₁ (rg x) = R₀ (rg x) := fun x hx =>
    ldlWX_rg hd hi wX R₀ xs _ h (fun k => hHne k x hx)
  have hR₁lr : ∀ y : LdlReg, y ≠ .dX → R₁ (lr y) = R₀ (lr y) := fun y hy =>
    ldlWX_lr hd hi wX R₀ xs _ h hy
  have hWM1 : ∀ j, W (xs.length + (j + 1)) = ldlWM rg lr (prime + Ka) n R₁ bs (j + 1) :=
    fun j => ldlWU_M _ _ _ _ _ _ _ _
  have h := layUnapply_exec_gen body hd pay hi hQ h.rg_inj hT (ldlPrepM rg lr) (ldlPrepX hd rg lr)
    (n := n) (K := K) hB xs bs hxs hbs W
    (fun j hj => by
      rw [hW, ldlWU_X _ _ _ _ _ _ _ (by omega : j + 1 ≤ xs.length)]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [ldlWX_rg hd hi wX R₀ xs _ h (fun k => hHk k pay (hpay k))]
        exact hb.bpay
      · intro j' hj'
        have hne : ∀ k, ldlH rg hd k ≠ rg (.sw j') := by
          intro k e
          have e1 := h.rg_inj e
          simp only [LayReg.sw.injEq] at e1
          have := (hd k).isLt
          rw [← e1, ldl_reg_val] at hj'
          omega
        rw [ldlWX_rg hd hi wX R₀ xs _ h hne]
        exact hb.bpriv j' hj'
      · intro k
        rw [show rg (.sw (reg (hd k))) = ldlH rg hd k from rfl, ldlWX_H hd hi wX R₀ xs j h k,
          List.getD_eq_getElem _ _ hj]
      · intro i hip hik
        rw [ldlWX_rg hd hi wX R₀ xs _ h (fun k => hHk k i (hik k))]
        exact hb.bother i hip hik
      · rw [ldlWX_rg hd hi wX R₀ xs _ h (fun k e => by have := h.rg_inj e; simp at this)]
        exact hb.tmp)
    (fun j hj => by
      rw [hWM1]
      have hg : bs.getD j (0, 0) = bs[j] := by rw [List.getD_eq_getElem _ _ hj]
      have e : ∀ x : LayReg t₀, x ≠ .mA → x ≠ .mB → (∀ i, x ≠ .sw i) →
          ldlWM rg lr (prime + Ka) n R₁ bs (j + 1) (rg x) = R₀ (rg x) := fun x h1 h2 h3 => by
        rw [ldlWM_rg n R₁ bs _ h h1 h2, hR₁rg x h3]
      exact ⟨by rw [e _ (by simp) (by simp) (by simp)]; exact hb.r0,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.r1,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.r2,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.r3,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.q0,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.q1,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.q2,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.q3,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.tmp,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.ctrB,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.cnt,
        by rw [e _ (by simp) (by simp) (by simp)]; exact hb.fld,
        by simp only [ldlWM]; rw [hg]; simp [Function.update_apply, h.rl, h.rg_inj.eq_iff],
        by simp only [ldlWM]; rw [hg]; simp [Function.update_apply, h.rl, h.rg_inj.eq_iff],
        fun r => by rw [e _ (by simp) (by simp) (by simp)]; exact hb.us r⟩)
    (fun _ => 14 * n + 12) (fun _ => 60 * wX + 75)
    (fun j hj => by
      rw [hW, ldlWU_X _ _ _ _ _ _ _ (by omega : j ≤ xs.length),
        ldlWU_X _ _ _ _ _ _ _ (by omega : j + 1 ≤ xs.length)]
      refine ldl_prepX_loads hA h hi hb.dX hb.cW hb.tA hb.tB hb.tS ?_ hwX hb.hdr hj
      intro d hd' k
      exact (hxs d hd').2.2.2 k)
    (fun j hj => by
      rw [hW, ldlWU_M, ldlWU_M, ← hR₁]
      refine ldl_prepM_loads hA h ?_ ?_ ?_ ?_ ?_ ?_ ?_ hj
      · rw [hR₁lr _ (by simp)]; exact hb.dM
      · rw [hR₁lr _ (by simp)]; exact hb.cN
      · rw [hR₁lr _ (by simp)]; exact hb.tA
      · rw [hR₁lr _ (by simp)]; exact hb.tB
      · rw [hR₁lr _ (by simp)]; exact hb.tS
      · rw [hR₁rg _ (by simp)]; exact hb.mA
      · rw [hR₁rg _ (by simp)]; exact hb.mB)
    l hl hlB h8 csM csX hcsM hcsX
  rw [hW0] at h
  exact h

variable {es : List ℕ} {ℓ K : ℕ}

/-- **The restoring stage of the layout `L`.** From a base file holding the description streams
of the inverse layout, `(layXcs es ℓ K B).reverse` (records of five words of `wX ≥ N + B + 2`
symbols) and `((layBits es ℓ K).map Prod.swap).reverse` (records of `N = es.sum` symbols), with
the counters `cM`, `cX` holding one symbol per move, `layUnapply` with the loaders leaves
`(moveRecs (layRec (layPerm es ℓ K)).symm l).flatten` on the stream register. -/
theorem sly_unstage_exec (H : LayHyp es ℓ K) (body : F → Pr F T Q (prime + Ka) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (h : LdlRegs rg lr) (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka)
    (hpay : ∀ k, hd k ≠ pay) {B : ℕ} (hB : 1 ≤ B) {wX : ℕ} (hwX : es.sum + B + 2 ≤ wX)
    (R₀ : Fin T → List (Fin (prime + Ka + 4)))
    (hb : LdlBase rg lr hd pay R₀ es.sum B wX ((layBits es ℓ K).map Prod.swap).reverse
      (layXcs es ℓ K B).reverse)
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ es.sum)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = (layBits es ℓ K).length)
    (hcsX : csX.length = (layXcs es ℓ K B).length) :
    LayRuns body (layUnapply hd pay hi hQ rg (fun _ _ e => by simpa using h.rg_inj e) hT
        (ldlPrepM rg lr) (ldlPrepX hd rg lr))
      (layDyn rg R₀ l.flatten csM [] csX [])
      (layDyn rg (ldlWU rg lr hd (prime + Ka) es.sum wX R₀ (layXcs es ℓ K B).reverse
          ((layBits es ℓ K).map Prod.swap).reverse
          ((layXcs es ℓ K B).length + (layBits es ℓ K).length))
        (moveRecs (layRec (layPerm es ℓ K)).symm l).flatten csM [] csX [])
      (layXcLoopCost T t₀ es.sum K B rg
          (ldlWU rg lr hd (prime + Ka) es.sum wX R₀ (layXcs es ℓ K B).reverse
            ((layBits es ℓ K).map Prod.swap).reverse)
          (fun _ => 60 * wX + 75) (layXcs es ℓ K B).reverse +
        layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length) := by
  have hbs : ∀ e ∈ ((layBits es ℓ K).map Prod.swap).reverse, e.1 < es.sum ∧ e.2 < es.sum := by
    intro e he
    simp only [List.mem_reverse, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨(layBits_valid H e' he').2, (layBits_valid H e' he').1⟩
  have hxs : ∀ d ∈ (layXcs es ℓ K B).reverse, d.OK es.sum K B := fun d hd =>
    layXcs_OK B H d (List.mem_reverse.1 hd)
  have hw : ∀ d ∈ (layXcs es ℓ K B).reverse, ∀ k, (d.hs k).length ≤ wX := fun d hd =>
    ldl_layXcs_hs_le H B wX hwX d (List.mem_reverse.1 hd)
  have hs := sly_unstage_gen body hd pay hi hQ h hT hA hpay hB _ _ hxs hbs hw R₀ hb l hl hlB h8
    csM csX (by simpa using hcsM) (by simpa using hcsX)
  rw [layStream, layMovesPerm_layUnapply B H, layRec_symm] at hs
  simpa using hs

end Stage

end IntegerMultBounds.MathlibTM2.Fast
