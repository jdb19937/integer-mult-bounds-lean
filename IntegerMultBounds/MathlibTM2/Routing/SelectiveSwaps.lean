module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveLayout
public import IntegerMultBounds.MathlibTM2.Node.CompactSwapPass

/-!
# Actual interchanges of the selective layout

The two swaps exchange b with t or u in the unchanged five-field bank. Their
complete host programs include symbol/bit conversion and the priced interchange.
Canonical header preparation is explicit caller work, not a free execution oracle.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable (p : Par) (X : ℕ)

def selectiveSwapOp (c : Fin 2) : Op := if c = 0 then .swapT else .swapU

def selectiveSwapFld (c : Fin 2) : Fin 5 := if c = 0 then 2 else 3

def selectiveSwapIdx (c : Fin 2) (i : ℕ) : ℕ :=
  selectiveIdx p X (fun _ => false) (fun _ _ _ => 0) (selectiveSwapOp c) i

theorem selectiveSwap_idx (c : Fin 2) (i : ℕ) :
    selectiveSwapIdx p X c i = swapIdx (selectiveLen p X) 0 (selectiveSwapFld c) i := by
  fin_cases c <;> rfl

theorem selectiveSwap_involutive (c : Fin 2) : Function.Involutive (selectiveSwapIdx p X c) := by
  intro i
  have heq : selectiveView p X (selectiveSwapIdx p X c (selectiveSwapIdx p X c i)) =
      selectiveView p X i := by
    unfold selectiveSwapIdx
    rw [selectiveView_idx, selectiveView_idx]
    fin_cases c <;> rfl
  apply eq_of_digit_eq (len := selectiveLen p X)
  · intro f
    fin_cases f
    · convert congrArg V.b heq using 1 <;> rfl
    · convert congrArg V.y heq using 1 <;> rfl
    · convert congrArg V.t heq using 1 <;> rfl
    · convert congrArg V.u heq using 1 <;> rfl
    · convert congrArg V.x heq using 1 <;> rfl
  · simp only [selectiveSwapIdx, selectiveIdx_div]

theorem selectiveSwap_lt (c : Fin 2) {R i : ℕ}
    (hi : i < R * 2 ^ fieldsLen (selectiveLen p X)) :
    selectiveSwapIdx p X c i < R * 2 ^ fieldsLen (selectiveLen p X) := by
  have hdiv := selectiveIdx_div p X (fun _ => false) (fun _ _ _ => 0) (selectiveSwapOp c) i
  have h := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ fieldsLen (selectiveLen p X))).2 hi
  rw [← hdiv] at h
  exact (Nat.div_lt_iff_lt_mul (by positivity)).1 h

def selectiveSwapPerm (R : ℕ) (c : Fin 2) : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))) where
  toFun i := ⟨selectiveSwapIdx p X c i, selectiveSwap_lt p X c i.isLt⟩
  invFun i := ⟨selectiveSwapIdx p X c i, selectiveSwap_lt p X c i.isLt⟩
  left_inv i := Fin.ext (selectiveSwap_involutive p X c i)
  right_inv i := Fin.ext (selectiveSwap_involutive p X c i)

def selectiveSwapHd (k : Fin 5) : Fin 6 := ⟨k.val, by omega⟩

def selectiveSwapPay : Fin 6 := 5

theorem selectiveSwapHd_inj : Function.Injective selectiveSwapHd := by
  intro k k' h
  have he := congrArg (fun x : Fin 6 => x.val) h
  exact Fin.ext he

variable {T Q K : ℕ} {P U : Type}

/-- Executed physical b/t or b/u interchange with its actual canonical header
values, symbol conversions, full frame and supplier-exponent cost. -/
theorem selectiveSwap_exec (body : P → Pr P T Q (prime + K) U) (c : Fin 2)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (bank : Fin (swapT 6) → Fin T) (hbank : Function.Injective bank) (hT : swapT 6 ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j, bank j ≠ str) (htmp : ∀ j, bank j ≠ tmp)
    {R B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = swapValues
      (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
        (fieldsLen (selectiveLen p X)) B).1
      (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
        (fieldsLen (selectiveLen p X)) B).2.1
      (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
        (fieldsLen (selectiveLen p X)) B).2.2 p.wc p.wc k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg selectiveSwapPay)) = [])
    (hpriv : ∀ j : Fin (swapT 6), 6 ≤ j.val → S.R (bank j) = [])
    (hhdr : ∀ k, S.R (bank (reg (selectiveSwapHd k))) = separator :: (hs k).map bitSymbol) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) *
        (R * 2 ^ fieldsLen (selectiveLen p X) * B : ℕ) *
          ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (S.R (bank j)).length + 34 * (R * 2 ^ fieldsLen (selectiveLen p X) * B) +
          2 * T + 6 * swapT 6 + 23 : ℕ) ∧
      Exec body (swapPass selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ
        bank hbank hT str tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (selectiveSwapPerm p X R c) l).flatten }) := by
  have hfld : selectiveLen p X (selectiveSwapFld c) = p.wc := by fin_cases c <;> rfl
  have horder : (0 : Fin 5) < selectiveSwapFld c := by fin_cases c <;> decide
  have hq : fieldOff (selectiveLen p X) (selectiveSwapFld c) + p.wc ≤
      fieldsLen (selectiveLen p X) := by
    rw [← hfld]
    exact fieldOff_add_le_total _ _
  apply cxSwap_exec body selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ bank hbank hT
    str tmp hst hstr htmp horder rfl hfld hR hq (selectiveSwapPerm p X R c)
    (fun r => selectiveSwap_idx p X c r) hB l hl hlB h8 hs hv hc v S hL hsrc htmp0 hpay0 hpriv hhdr
  intro i hip hhd s _
  have hi : i.val < 5 := by
    have hne : i.val ≠ 5 := fun he => hip (Fin.ext he)
    omega
  exact (hhd ⟨i.val, hi⟩ (Fin.ext rfl)).elim

end IntegerMultBounds.MathlibTM2.Routing
