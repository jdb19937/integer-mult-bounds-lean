module

public import IntegerMultBounds.MathlibTM2.Fast.SynBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Runtime unary arithmetic for compact stage descriptors. The arity `m` is a
fixed machine constant; lengths, offsets, and chunk sizes are runtime inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {T Q A : ℕ} {U P : Type}

/-- Roles: numerator, divisor, quotient, remainder, three scratch registers. -/
def compactDescriptorQuotient (e : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (synDivModR (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6)) (uclear (e 3))

def compactDescriptorQuotientCost (x k : ℕ) := synDivModCost x k+2*(x%k)+2

theorem compactDescriptorQuotient_runs (body : P → Pr P T Q A U)
    (e : Fin 7 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (hk : 1 ≤ (R (e 1)).length)
    (hz : ∀ i : Fin 7,2 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorQuotient e) R
      (Function.update R (e 2) (List.replicate ((R (e 0)).length/(R (e 1)).length) tick))
      (compactDescriptorQuotientCost (R (e 0)).length (R (e 1)).length) := by
  have h2 := hz 2 (by decide); have h3 := hz 3 (by decide)
  have h4 := hz 4 (by decide); have h5 := hz 5 (by decide); have h6 := hz 6 (by decide)
  have hd : [e 0,e 1,e 2,e 3,e 4,e 5,e 6].Nodup := by
    simpa using (show ([0,1,2,3,4,5,6] : List (Fin 7)).Nodup by decide).map he
  refine lr_weaken body ((lr_synDivModR body hd hk h3 h4 h5 h6).seq (lr_uclear body (e 3))) ?_ ?_
  · funext z
    by_cases hze : z=e 2
    · subst z; simp [he.eq_iff,h2]
    by_cases hz3 : z=e 3
    · subst z; simp [he.eq_iff,h3]
    simp [Function.update_of_ne,hze,hz3]
  · simp [he.eq_iff,compactDescriptorQuotientCost,Nat.add_assoc]

/-- Inputs 0,1: node bit length and chunk. Output 2: slot width.
Temporary denominator 3 and all remaining scratch are restored empty. -/
def compactDescriptorWidth (e : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (umul m (e 1) (e 3) (e 5)) <|
  .seq (compactDescriptorQuotient (fun i => e (![0,3,2,4,5,6,7] i))) (uclear (e 3))

def compactDescriptorWidthCost (length chunk : ℕ) :=
  (4*chunk+4)+compactDescriptorQuotientCost length (m*chunk)+(2*(m*chunk)+2)

theorem compactDescriptorWidth_runs (body : P → Pr P T Q A U)
    (e : Fin 8 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (hk : 1 ≤ m*(R (e 1)).length)
    (hz : ∀ i : Fin 8,2 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorWidth e) R
      (Function.update R (e 2) (List.replicate ((R (e 0)).length/(m*(R (e 1)).length)) tick))
      (compactDescriptorWidthCost (R (e 0)).length (R (e 1)).length) := by
  have h2 := hz 2 (by decide); have h3 := hz 3 (by decide)
  have h4 := hz 4 (by decide); have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide); have h7 := hz 7 (by decide)
  refine lr_weaken body
    ((lr_umul body m (a:=e 1) (b:=e 3) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) h5).seq <|
    (compactDescriptorQuotient_runs body (fun i => e (![0,3,2,4,5,6,7] i))
      (he.comp (by decide)) _ (by simpa [h3] using hk)
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    lr_uclear body (e 3)) ?_ ?_
  · funext z
    by_cases hz2 : z=e 2
    · subst z; simp [he.eq_iff,h3]
    by_cases hz3 : z=e 3
    · subst z; simp [he.eq_iff,h3]
    simp [Function.update_of_ne,hz2,hz3]
  · simp [he.eq_iff,h3,compactDescriptorWidthCost,Nat.add_assoc]

end
end IntegerMultBounds.MathlibTM2.Node
