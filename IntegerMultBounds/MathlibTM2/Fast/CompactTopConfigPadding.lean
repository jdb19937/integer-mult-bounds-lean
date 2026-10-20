module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecArithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.Compact.Layout

/-! Exact runtime rounding of the actual row stock to a runtime divisor.
Both inputs are preserved, and all temporary registers are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

theorem compactTopConfig_ceil_mul (x k : ℕ) (hk : 0<k) :
    chunks x k*k = Compact.Layout.paddedRows x k := by
  obtain ⟨hx,hlt⟩ := Compact.Layout.ceiling_chunks x k hk
  obtain ⟨hp,hplt,hpd⟩ := Compact.Layout.paddedRows_bounds x k hk
  have hcd : k ∣ chunks x k*k := dvd_mul_left k (chunks x k)
  change x ≤ chunks x k*k at hx
  change chunks x k*k < x+k at hlt
  by_cases h : Compact.Layout.paddedRows x k ≤ chunks x k*k
  · have hd := Nat.dvd_sub hcd hpd
    have he := Nat.eq_zero_of_dvd_of_lt hd (by omega : chunks x k*k-Compact.Layout.paddedRows x k < k)
    omega
  · have hd := Nat.dvd_sub hpd hcd
    have he := Nat.eq_zero_of_dvd_of_lt hd (by omega : Compact.Layout.paddedRows x k-chunks x k*k < k)
    omega

/-- Roles: row stock, divisor, padded result, quotient, and five scratch tapes. -/
def compactTopConfigPadding (e : Fin 9 → SynW) : Pr P (nT SXReg) Q A U :=
  .seq (compactCeil (fun i => e (![0,1,3,4,5,6,7,8] i))) <|
  .seq (synMulR (sreg (e 3)) (sreg (e 1)) (sreg (e 2)) (sreg (e 6)) (sreg (e 7)))
    (uclear (sreg (e 3)))

def compactTopConfigPaddingCost (x k : ℕ) : ℕ :=
  compactCeilCost x k+(synMulRCost (chunks x k) k+(2*chunks x k+2))

theorem sg_compactTopConfigPadding (body : P → Pr P (nT SXReg) Q A U)
    (e : Fin 9 → SynW) (he : Function.Injective e)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (x k : ℕ) (hk : 1≤k) (hx : (v (e 0)).length=x) (hkv : (v (e 1)).length=k)
    (hz : ∀ i : Fin 9, 2 ≤ i.val → v (e i)=[]) :
    LayRuns body (compactTopConfigPadding e) (synG R v)
      (synG R (Function.update v (e 2) (List.replicate (Compact.Layout.paddedRows x k) tick)))
      (compactTopConfigPaddingCost x k) := by
  have h2 := hz 2 (by decide)
  have h3 := hz 3 (by decide)
  have h6 := hz 6 (by decide)
  have h7 := hz 7 (by decide)
  have hc := sg_compactCeil body (fun i => e (![0,1,3,4,5,6,7,8] i))
    (he.comp (by decide)) R v x k hk hx hkv
    (by
      intro i hi
      have hin : ∀ i : Fin 8, 2 ≤ i.val → 2 ≤ (![0,1,3,4,5,6,7,8] i : Fin 9).val := by decide
      exact hz _ (hin i hi))
  have hreg : [e 3,e 1,e 2,e 6,e 7].Nodup := by
    simpa only [List.map_cons,List.map_nil] using
      (show ([3,1,2,6,7] : List (Fin 9)).Nodup by decide).map he
  refine lr_weaken body (hc.seq <|
    (sgU_mulR body (a := e 3) (b := e 1) (c := e 2) (t₁ := e 6) (t₂ := e 7)
      (x := chunks x k) (y := k) (z := 0) hreg
      (by simp [he.eq_iff,h6]) (by simp [he.eq_iff,h7])
      (by simp) (by simp [he.eq_iff,hkv]) (by simp [he.eq_iff,h2])).seq <|
    sgU_clear body (a := e 3) (x := chunks x k) (by simp [he.eq_iff])) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  by_cases hze : z=e 2
  · subst z; simp [he.eq_iff,compactTopConfig_ceil_mul x k (by omega)]
  by_cases hz3 : z=e 3
  · subst z; simp [he.eq_iff,h3]
  simp [Function.update_of_ne,hze,hz3]

end
end IntegerMultBounds.MathlibTM2.Fast
