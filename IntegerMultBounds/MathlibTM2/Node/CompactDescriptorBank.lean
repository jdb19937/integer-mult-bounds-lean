module

public import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorBankOps
public import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorPadding
public import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A complete runtime unary source bank for all thirteen native descriptors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section
variable {T Q A : ℕ} {U P : Type}

/-- Inputs: length, chunk, absolute offset, low offset, back bits, active, total
bits, shape bits, outside rows, coefficient count, coefficient width, source,
target, axes, guard, residue. -/
def compactDescriptorBankValues (v : Fin 16 → ℕ) : Fin 8 → ℕ :=
  let width := v 0/(m*v 1)
  let right := (v 2-v 3-v 4)/v 1
  ![width,right,v 5-m*width-right,2^(v 6-v 3-v 7)*v 8,
    2^(v 3)*(3*(v 9*v 10)),m,m-1-v 11,m-1-v 12]

/-- The five original global values are aliases; the other eight are computed. -/
def compactDescriptorBankSources (e : Fin 30 → Fin T) : Fin 13 → Fin T :=
  fun i => e (![1,13,14,5,19,20,21,16,18,17,15,22,23] i)

def compactDescriptorBankOriginals (v : Fin 16 → ℕ) : Fin 13 → ℕ :=
  let b := compactDescriptorBankValues v
  ![v 1,v 13,v 14,v 5,b 3,b 4,b 5,b 0,b 2,b 1,v 15,b 6,b 7]

def compactDescriptorBankState (e : Fin 30 → Fin T)
    (R : Fin T → List (Fin (A+4))) : Fin T → List (Fin (A+4)) :=
  let v := fun i : Fin 16 => (R (e (Fin.castAdd 14 i))).length
  let b := compactDescriptorBankValues v
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update R
    (e 16) (List.replicate (b 0) tick)) (e 17) (List.replicate (b 1) tick))
    (e 18) (List.replicate (b 2) tick)) (e 19) (List.replicate (b 3) tick))
    (e 20) (List.replicate (b 4) tick)) (e 21) (List.replicate (b 5) tick))
    (e 22) (List.replicate (b 6) tick)) (e 23) (List.replicate (b 7) tick)

/-- All dimensions are runtime source lengths. Only the fixed arity is compiled.
Roles 0–15 are preserved inputs, 16–23 outputs, 24–29 restored scratch. -/
def compactDescriptorBankProg (e : Fin 30 → Fin T) : Pr P T Q A U :=
  .seq (compactDescriptorStage (fun i => e (![0,1,2,3,4,5,16,17,18,24,25,26,27,28,29] i))) <|
  .seq (compactDescriptorRows (fun i => e (![6,3,7,8,19,25,27,28] i))) <|
  .seq (compactDescriptorPayload (fun i => e (![3,9,10,20,24,27,28] i))) <|
  .seq (compactDescriptorConst m (e 21)) <|
  .seq (compactDescriptorReverse (fun i => e (![11,22,27] i)))
    (compactDescriptorReverse (fun i => e (![12,23,27] i)))

def compactDescriptorBankCost (v : Fin 16 → ℕ) :=
  compactDescriptorStageCost (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)+
  compactDescriptorRowsCost (v 6) (v 3) (v 7) (v 8)+
  compactDescriptorPayloadCost (v 3) (v 9) (v 10)+1+
  (1+(4*v 11+4))+(1+(4*v 12+4))

theorem compactDescriptorBank_runs (body : P → Pr P T Q A U)
    (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (hk : 1 ≤ (R (e 1)).length)
    (hz : ∀ i : Fin 30, 16 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorBankProg e) R (compactDescriptorBankState e R)
      (compactDescriptorBankCost (fun i => (R (e (Fin.castAdd 14 i))).length)) := by
  have h16 := hz 16 (by decide); have h17 := hz 17 (by decide); have h18 := hz 18 (by decide)
  have h19 := hz 19 (by decide); have h20 := hz 20 (by decide); have h21 := hz 21 (by decide)
  have h22 := hz 22 (by decide); have h23 := hz 23 (by decide); have h24 := hz 24 (by decide)
  have h25 := hz 25 (by decide); have h26 := hz 26 (by decide); have h27 := hz 27 (by decide)
  have h28 := hz 28 (by decide); have h29 := hz 29 (by decide)
  refine lr_weaken body
    ((compactDescriptorStage_runs body
      (fun i => e (![0,1,2,3,4,5,16,17,18,24,25,26,27,28,29] i))
      (he.comp (by decide)) R hk
      (by intro i hi; fin_cases i <;> simp_all)).seq <|
    (compactDescriptorRows_runs body (fun i => e (![6,3,7,8,19,25,27,28] i))
      (he.comp (by decide)) _ (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    (compactDescriptorPayload_runs body (fun i => e (![3,9,10,20,24,27,28] i))
      (he.comp (by decide)) _ (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    (compactDescriptorConst_runs body m (e 21) _).seq <|
    (compactDescriptorReverse_runs body (fun i => e (![11,22,27] i))
      (he.comp (by decide)) _ (by simp [he.eq_iff,h22]) (by simp [he.eq_iff,h27])).seq <|
    compactDescriptorReverse_runs body (fun i => e (![12,23,27] i))
      (he.comp (by decide)) _ (by simp [he.eq_iff,h23]) (by simp [he.eq_iff,h27])) ?_ ?_
  · simp [compactDescriptorBankState,compactDescriptorBankValues,he.eq_iff,h21]
  · simp [compactDescriptorBankCost,he.eq_iff,Nat.add_assoc]

/-- Direct source-length interface consumed by `compactSlotPrepared_exec`. -/
theorem compactDescriptorBank_lengths (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (i : Fin 13) :
    ((compactDescriptorBankState e R) (compactDescriptorBankSources e i)).length =
      compactDescriptorBankOriginals (fun j => (R (e (Fin.castAdd 14 j))).length) i := by
  fin_cases i <;>
    simp [compactDescriptorBankState,compactDescriptorBankSources,compactDescriptorBankOriginals,
      compactDescriptorBankValues,he.eq_iff]

/-- Literal preservation of every input and scratch register, and all outside registers. -/
theorem compactDescriptorBank_frame (e : Fin 30 → Fin T)
    (R : Fin T → List (Fin (A+4))) (z : Fin T)
    (hz : ∀ i : Fin 30, 16 ≤ i.val → i.val < 24 → z≠e i) :
    compactDescriptorBankState e R z=R z := by
  have h0 := hz 16 (by decide) (by decide); have h1 := hz 17 (by decide) (by decide)
  have h2 := hz 18 (by decide) (by decide); have h3 := hz 19 (by decide) (by decide)
  have h4 := hz 20 (by decide) (by decide); have h5 := hz 21 (by decide) (by decide)
  have h6 := hz 22 (by decide) (by decide); have h7 := hz 23 (by decide) (by decide)
  simp [compactDescriptorBankState,Function.update_of_ne,h0,h1,h2,h3,h4,h5,h6,h7]

/-- Concrete runtime input lengths for a recursive node after absorbing low
address digits into the payload. No dimension is a program parameter. -/
def compactDescriptorBankInputs {s : Shape} {n a₀ k ρ left right : ℕ}
    (_layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o R r w : ℕ) (x y : Fin m) : Fin 16 → ℕ :=
  ![s.chunk*(m*k),s.chunk,o+a₀,o,s.H+s.B,s.active,o+n,s.bits,R,r,w,
    x.val,y.val,s.axes,s.guard,ρ]

/-- The computed bank equals all thirteen original native descriptors, including
reversed slot numbering and the rows/payload split caused by low-offset absorption. -/
theorem compactDescriptorBank_originals {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o R r w : ℕ) (x y : Fin m) (hxy : x≠y)
    (hpayload : s.payload=2^o*(3*(r*w))) :
    compactDescriptorBankOriginals (compactDescriptorBankInputs layout o R r w x y) =
      ActivePrefixStageHeadersData.originalValues (compactRecursiveStage layout x y hxy)
        (2^(n-s.bits)*R) := by
  have hK : 0<s.chunk := lt_of_le_of_lt (Nat.zero_le ρ) layout.selectedFits
  have hex := compactDescriptorStage_exact s.chunk k left right o (s.H+s.B) hK
  have hw : s.chunk*(m*k)/(m*s.chunk)=k := hex.1
  have hr : (o+a₀-o-(s.H+s.B))/s.chunk=right := by
    rw [layout.lowReserve]
    simpa only [Nat.mul_comm, Nat.add_assoc] using hex.2.1
  have hr' : (a₀-(s.H+s.B))/s.chunk=right := by simpa using hr
  have hl : s.active-m*k-right=left := by rw [layout.active]; omega
  have hm73 : m = 73 := rfl
  funext i
  fin_cases i <;>
    simp [compactDescriptorBankOriginals,compactDescriptorBankValues,compactDescriptorBankInputs,
      ActivePrefixStageHeadersData.originalValues,compactRecursiveStage,hw,hr',hl,hpayload,Fin.rev] <;> omega

/-- Ready-to-use header source length facts for the prepared slot executor. -/
theorem compactDescriptorBank_original_lengths {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o rowCount r w : ℕ) (x y : Fin m) (hxy : x≠y)
    (hpayload : s.payload=2^o*(3*(r*w)))
    (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4)))
    (hin : ∀ i : Fin 16,(R (e (Fin.castAdd 14 i))).length =
      compactDescriptorBankInputs layout o rowCount r w x y i) (i : Fin 13) :
    ((compactDescriptorBankState e R) (compactDescriptorBankSources e i)).length =
      ActivePrefixStageHeadersData.originalValues (compactRecursiveStage layout x y hxy)
        (2^(n-s.bits)*rowCount) i := by
  rw [compactDescriptorBank_lengths e he R i]
  have hv : (fun j : Fin 16 => (R (e (Fin.castAdd 14 j))).length) =
      compactDescriptorBankInputs layout o rowCount r w x y := funext hin
  rw [hv,compactDescriptorBank_originals layout o rowCount r w x y hxy hpayload]

end
end IntegerMultBounds.MathlibTM2.Node
