module

public import IntegerMultBounds.Machine.CompactGadgetReservationCapacity
public import IntegerMultBounds.MathlibTM2.Fast.SynBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat

/-! # Runtime arithmetic for the reserved layer records

The ceiling quotient is computed from unary runtime registers. Source registers
are preserved literally and every temporary register returns empty.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Roles: numerator source, divisor, result, sum, remainder, three scratch registers. -/
def compactCeil (e : Fin 8 → SynW) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (e 0)) (sreg (e 3)) (sreg (e 5))) <|
  .seq (ucopy (sreg (e 1)) (sreg (e 3)) (sreg (e 5))) <|
  .seq (synPop (sreg (e 3))) <|
  .seq (synDivModR (sreg (e 3)) (sreg (e 1)) (sreg (e 2)) (sreg (e 4))
    (sreg (e 5)) (sreg (e 6)) (sreg (e 7))) <|
  .seq (uclear (sreg (e 3))) (uclear (sreg (e 4)))

def compactCeilCost (x k : ℕ) : ℕ :=
  (4*x+4)+(4*k+4)+1+synDivModCost (x+k-1) k+
    (2*(x+k-1)+2)+(2*((x+k-1)%k)+2)

theorem sg_compactCeil (body : P → Pr P (nT SXReg) Q A U)
    (e : Fin 8 → SynW) (he : Function.Injective e)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (x k : ℕ) (hk : 1 ≤ k) (hx : (v (e 0)).length=x) (hkv : (v (e 1)).length=k)
    (hz : ∀ i : Fin 8, 2 ≤ i.val → v (e i)=[]) :
    LayRuns body (compactCeil e) (synG R v)
      (synG R (Function.update v (e 2)
        (List.replicate (CompactGadgetReservationCapacity.chunks x k) tick)))
      (compactCeilCost x k) := by
  have h2 := hz 2 (by decide)
  have h3 := hz 3 (by decide)
  have h4 := hz 4 (by decide)
  have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide)
  have h7 := hz 7 (by decide)
  have hreg : [e 3,e 1,e 2,e 4,e 5,e 6,e 7].Nodup := by
    simpa only [List.map_cons,List.map_nil] using
      (show ([3,1,2,4,5,6,7] : List (Fin 8)).Nodup by decide).map he
  refine lr_weaken body
    ((sgU_copy body (R := R) (v := v) (a := e 0) (b := e 3) (t := e 5) (x := x) (y := 0)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) h5 hx (by simpa using h3)).seq <|
    (sgU_copy body (a := e 1) (b := e 3) (t := e 5) (x := k) (y := x)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h5]) (by simp [he.eq_iff,hkv]) (by simp)).seq <|
    (sgU_pop body (a := e 3) (y := k+x) (by simp)).seq <|
    (sgU_divMod body (x := e 3) (k := e 1) (q := e 2) (r := e 4)
      (t₁ := e 5) (t₂ := e 6) (t₃ := e 7) (X := x+k-1) (Kv := k) (z := 0)
      hreg hk (by simp [he.eq_iff,hkv]) (by simp [Nat.add_comm])
      (by simp [he.eq_iff,h4]) (by simp [he.eq_iff,h2])
      (by simp [he.eq_iff,h5]) (by simp [he.eq_iff,h6]) (by simp [he.eq_iff,h7])).seq <|
    (sgU_clear body (a := e 3) (x := x+k-1) (by simp [he.eq_iff,Nat.add_comm])).seq <|
    sgU_clear body (a := e 4) (x := (x+k-1)%k) (by simp [he.eq_iff])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hze : z=e 2
    · subst z; simp [he.eq_iff,CompactGadgetReservationCapacity.chunks]
    by_cases hz3 : z=e 3
    · subst z; simp [he.eq_iff,h3]
    by_cases hz4 : z=e 4
    · subst z; simp [he.eq_iff,h4]
    simp [Function.update_of_ne,hze,hz3,hz4]
  · simp only [compactCeilCost]
    omega


/-- Input roles 0–5: axes, guard, chunk, selected count, row axes, low offset.
Output roles 6–9: front chunks, back chunks, active count, active offset.
Roles 10–16 are empty scratch, restored after the computation. -/
def compactReserveCounts (e : Fin 17 → SynW) : Pr P (nT SXReg) Q A U :=
  .seq (synMulR (sreg (e 0)) (sreg (e 1)) (sreg (e 10)) (sreg (e 14)) (sreg (e 15))) <|
  .seq (umul 2 (sreg (e 10)) (sreg (e 11)) (sreg (e 14))) <|
  .seq (compactCeil (fun i => e (![11,2,6,12,13,14,15,16] i))) <|
  .seq (compactCeil (fun i => e (![10,2,7,12,13,14,15,16] i))) <|
  .seq (ucopy (sreg (e 3)) (sreg (e 8)) (sreg (e 14))) <|
  .seq (usub (sreg (e 4)) (sreg (e 8)) (sreg (e 14))) <|
  .seq (usub (sreg (e 6)) (sreg (e 8)) (sreg (e 14))) <|
  .seq (usub (sreg (e 7)) (sreg (e 8)) (sreg (e 14))) <|
  .seq (synMulR (sreg (e 2)) (sreg (e 7)) (sreg (e 9)) (sreg (e 14)) (sreg (e 15))) <|
  .seq (ucopy (sreg (e 5)) (sreg (e 9)) (sreg (e 14))) <|
  .seq (uclear (sreg (e 10))) (uclear (sreg (e 11)))

def compactReserveCountsCost (d g k D q o : ℕ) : ℕ :=
  let f := CompactGadgetReservationCapacity.frontChunks d g k
  let b := CompactGadgetReservationCapacity.backChunks d g k
  synMulRCost d g+(4*(d*g)+4)+compactCeilCost (2*(d*g)) k+compactCeilCost (d*g) k+
    (4*D+4)+(4*q+4)+(4*f+4)+(4*b+4)+synMulRCost k b+(4*o+4)+
    (2*(d*g)+2)+(2*(2*(d*g))+2)

theorem sg_compactReserveCounts (body : P → Pr P (nT SXReg) Q A U)
    (e : Fin 17 → SynW) (he : Function.Injective e)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g k D q o : ℕ) (hk : 1≤k)
    (hi : ∀ i : Fin 6, (v (e (Fin.castAdd 11 i))).length = ![d,g,k,D,q,o] i)
    (hz : ∀ i : Fin 17, 6 ≤ i.val → v (e i)=[]) :
    let f := CompactGadgetReservationCapacity.frontChunks d g k
    let b := CompactGadgetReservationCapacity.backChunks d g k
    LayRuns body (compactReserveCounts e) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (e 6) (List.replicate f tick)) (e 7) (List.replicate b tick))
        (e 8) (List.replicate (D-q-f-b) tick)) (e 9) (List.replicate (o+k*b) tick)))
      (compactReserveCountsCost d g k D q o) := by
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2
  have h3 := hi 3; have h4 := hi 4; have h5 := hi 5
  change (v (e 0)).length = d at h0
  change (v (e 1)).length = g at h1
  change (v (e 2)).length = k at h2
  change (v (e 3)).length = D at h3
  change (v (e 4)).length = q at h4
  change (v (e 5)).length = o at h5
  have z6 := hz 6 (by decide); have z7 := hz 7 (by decide)
  have z8 := hz 8 (by decide); have z9 := hz 9 (by decide)
  have z10 := hz 10 (by decide); have z11 := hz 11 (by decide)
  have z12 := hz 12 (by decide); have z13 := hz 13 (by decide)
  have z14 := hz 14 (by decide); have z15 := hz 15 (by decide); have z16 := hz 16 (by decide)
  have hf : CompactGadgetReservationCapacity.chunks (2*(d*g)) k =
      CompactGadgetReservationCapacity.frontChunks d g k := rfl
  have hb : CompactGadgetReservationCapacity.chunks (d*g) k =
      CompactGadgetReservationCapacity.backChunks d g k := rfl
  refine lr_weaken body
    ((sgU_mulR body (R := R) (v := v) (a := e 0) (b := e 1) (c := e 10)
      (t₁ := e 14) (t₂ := e 15) (x := d) (y := g) (z := 0)
      (by simpa using (show ([0,1,10,14,15] : List (Fin 17)).Nodup by decide).map he)
      z14 z15 h0 h1 (by simpa using z10)).seq <|
    (sgU_umul body 2 (a := e 10) (b := e 11) (t := e 14) (x := d*g) (y := 0)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp) (by simp [he.eq_iff,z11])).seq <|
    (sg_compactCeil body (fun i => e (![11,2,6,12,13,14,15,16] i))
      (he.comp (by decide)) R _ (2*(d*g)) k hk (by simp) (by simp [he.eq_iff,h2])
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    (sg_compactCeil body (fun i => e (![10,2,7,12,13,14,15,16] i))
      (he.comp (by decide)) R _ (d*g) k hk (by simp [he.eq_iff]) (by simp [he.eq_iff,h2])
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    (sgU_copy body (a := e 3) (b := e 8) (t := e 14) (x := D) (y := 0)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,h3]) (by simp [he.eq_iff,z8])).seq <|
    (sgU_sub body (a := e 4) (b := e 8) (t := e 14) (x := q) (y := D)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,h4]) (by simp)).seq <|
    (sgU_sub body (a := e 6) (b := e 8) (t := e 14)
      (x := CompactGadgetReservationCapacity.frontChunks d g k) (y := D-q)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,hf]) (by simp)).seq <|
    (sgU_sub body (a := e 7) (b := e 8) (t := e 14)
      (x := CompactGadgetReservationCapacity.backChunks d g k)
      (y := D-q-CompactGadgetReservationCapacity.frontChunks d g k)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,hb]) (by simp)).seq <|
    (sgU_mulR body (a := e 2) (b := e 7) (c := e 9) (t₁ := e 14) (t₂ := e 15)
      (x := k) (y := CompactGadgetReservationCapacity.backChunks d g k) (z := 0)
      (by simpa using (show ([2,7,9,14,15] : List (Fin 17)).Nodup by decide).map he)
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,z15])
      (by simp [he.eq_iff,h2]) (by simp [he.eq_iff,hb]) (by simp [he.eq_iff,z9])).seq <|
    (sgU_copy body (a := e 5) (b := e 9) (t := e 14) (x := o)
      (y := k*CompactGadgetReservationCapacity.backChunks d g k)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,z14]) (by simp [he.eq_iff,h5]) (by simp)).seq <|
    (sgU_clear body (a := e 10) (x := d*g) (by simp [he.eq_iff])).seq <|
    sgU_clear body (a := e 11) (x := 2*(d*g)) (by simp [he.eq_iff])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [he.eq_iff]
  · simp only [compactReserveCountsCost]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
