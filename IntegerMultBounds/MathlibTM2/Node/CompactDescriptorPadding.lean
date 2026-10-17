module

public import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorArithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Runtime left and right stage padding from reservation and node counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {T Q A : ℕ} {U P : Type}

/-- Inputs 0–3: absolute offset, low offset, reserved back bits, chunk.
Output 4: right padding. Roles 5–9 are restored empty. -/
def compactDescriptorRight (e : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (ucopy (e 0) (e 5) (e 7)) <|
  .seq (usub (e 1) (e 5) (e 7)) <|
  .seq (usub (e 2) (e 5) (e 7)) <|
  .seq (compactDescriptorQuotient (fun i => e (![5,3,4,6,7,8,9] i))) (uclear (e 5))

def compactDescriptorRightCost (a₀ o back chunk : ℕ) :=
  (4*a₀+4)+(4*o+4)+(4*back+4)+
    compactDescriptorQuotientCost (a₀-o-back) chunk+(2*(a₀-o-back)+2)

theorem compactDescriptorRight_runs (body : P → Pr P T Q A U)
    (e : Fin 10 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (hk : 1 ≤ (R (e 3)).length)
    (hz : ∀ i : Fin 10, 4 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorRight e) R
      (Function.update R (e 4) (List.replicate
        (((R (e 0)).length-(R (e 1)).length-(R (e 2)).length)/(R (e 3)).length) tick))
      (compactDescriptorRightCost (R (e 0)).length (R (e 1)).length
        (R (e 2)).length (R (e 3)).length) := by
  have h4 := hz 4 (by decide); have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide); have h7 := hz 7 (by decide)
  have h8 := hz 8 (by decide); have h9 := hz 9 (by decide)
  refine lr_weaken body
    ((lr_ucopy body (R:=R) (a:=e 0) (b:=e 5) (t:=e 7)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) h7).seq <|
    (lr_usub body (a:=e 1) (b:=e 5) (t:=e 7)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h7])).seq <|
    (lr_usub body (a:=e 2) (b:=e 5) (t:=e 7)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h7])).seq <|
    (compactDescriptorQuotient_runs body (fun i => e (![5,3,4,6,7,8,9] i))
      (he.comp (by decide)) _ (by simpa [he.eq_iff] using hk)
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    lr_uclear body (e 5)) ?_ ?_
  · funext z
    by_cases hz4 : z=e 4
    · subst z; simp [he.eq_iff,h5,List.drop_replicate]
    by_cases hz5 : z=e 5
    · subst z; simp [he.eq_iff,h5]
    simp [Function.update_of_ne,hz4,hz5]
  · simp [he.eq_iff,h5,List.drop_replicate,compactDescriptorRightCost,Nat.add_assoc]

/-- Inputs 0–2: active chunks, slot width, right padding. Output 3: left
padding. Temporary product 4 and scratch 5 are restored empty. -/
def compactDescriptorLeft (e : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (ucopy (e 0) (e 3) (e 5)) <|
  .seq (umul m (e 1) (e 4) (e 5)) <|
  .seq (usub (e 4) (e 3) (e 5)) <|
  .seq (usub (e 2) (e 3) (e 5)) (uclear (e 4))

def compactDescriptorLeftCost (active width right : ℕ) :=
  (4*active+4)+(4*width+4)+(4*(m*width)+4)+(4*right+4)+(2*(m*width)+2)

theorem compactDescriptorLeft_runs (body : P → Pr P T Q A U)
    (e : Fin 6 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4)))
    (hz : ∀ i : Fin 6, 3 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorLeft e) R
      (Function.update R (e 3) (List.replicate
        ((R (e 0)).length-m*(R (e 1)).length-(R (e 2)).length) tick))
      (compactDescriptorLeftCost (R (e 0)).length (R (e 1)).length (R (e 2)).length) := by
  have h3 := hz 3 (by decide); have h4 := hz 4 (by decide); have h5 := hz 5 (by decide)
  refine lr_weaken body
    ((lr_ucopy body (R:=R) (a:=e 0) (b:=e 3) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) h5).seq <|
    (lr_umul body m (a:=e 1) (b:=e 4) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h5])).seq <|
    (lr_usub body (a:=e 4) (b:=e 3) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h5])).seq <|
    (lr_usub body (a:=e 2) (b:=e 3) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h5])).seq <|
    lr_uclear body (e 4)) ?_ ?_
  · funext z
    by_cases hz3 : z=e 3
    · subst z; simp [he.eq_iff,h3,h4,List.drop_replicate]
    by_cases hz4 : z=e 4
    · subst z; simp [he.eq_iff,h4]
    simp [Function.update_of_ne,hz3,hz4]
  · simp [he.eq_iff,h3,h4,List.drop_replicate,compactDescriptorLeftCost,Nat.add_assoc]

/-- Inputs 0–5 are node length, chunk, absolute offset, low offset, reserved back
bits, and global active chunks. Outputs 6–8 are width, right, left. Roles 9–14
are scratch, restored empty. -/
def compactDescriptorStage (e : Fin 15 → Fin T) : Pr P T Q A U :=
  .seq (compactDescriptorWidth (fun i => e (![0,1,6,9,11,12,13,14] i))) <|
  .seq (compactDescriptorRight (fun i => e (![2,3,4,1,7,10,11,12,13,14] i)))
    (compactDescriptorLeft (fun i => e (![5,6,7,8,9,12] i)))

def compactDescriptorStageCost (length chunk a₀ o back active : ℕ) :=
  compactDescriptorWidthCost length chunk+
  compactDescriptorRightCost a₀ o back chunk+
  compactDescriptorLeftCost active (length/(m*chunk)) ((a₀-o-back)/chunk)

theorem compactDescriptorStage_runs (body : P → Pr P T Q A U)
    (e : Fin 15 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (hk : 1 ≤ (R (e 1)).length)
    (hz : ∀ i : Fin 15, 6 ≤ i.val → R (e i)=[]) :
    let width := (R (e 0)).length/(m*(R (e 1)).length)
    let right := ((R (e 2)).length-(R (e 3)).length-(R (e 4)).length)/(R (e 1)).length
    LayRuns body (compactDescriptorStage e) R
      (Function.update (Function.update (Function.update R
        (e 6) (List.replicate width tick)) (e 7) (List.replicate right tick))
        (e 8) (List.replicate ((R (e 5)).length-m*width-right) tick))
      (compactDescriptorStageCost (R (e 0)).length (R (e 1)).length
        (R (e 2)).length (R (e 3)).length (R (e 4)).length (R (e 5)).length) := by
  have h6 := hz 6 (by decide); have h7 := hz 7 (by decide); have h8 := hz 8 (by decide)
  have h9 := hz 9 (by decide); have h10 := hz 10 (by decide); have h11 := hz 11 (by decide)
  have h12 := hz 12 (by decide); have h13 := hz 13 (by decide); have h14 := hz 14 (by decide)
  dsimp only
  refine lr_weaken body
    ((compactDescriptorWidth_runs body (fun i => e (![0,1,6,9,11,12,13,14] i))
      (he.comp (by decide)) R (by change 1 ≤ m*(R (e 1)).length; exact Nat.mul_pos (by decide : 0 < m) hk)
      (by intro i hi; fin_cases i <;> simp_all)).seq <|
    (compactDescriptorRight_runs body (fun i => e (![2,3,4,1,7,10,11,12,13,14] i))
      (he.comp (by decide)) _ (by simpa [he.eq_iff] using hk)
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])).seq <|
    compactDescriptorLeft_runs body (fun i => e (![5,6,7,8,9,12] i))
      (he.comp (by decide)) _
      (by intro i hi; fin_cases i <;> simp_all [he.eq_iff])) ?_ ?_
  · simp [he.eq_iff]
  · simp [he.eq_iff,compactDescriptorStageCost,Nat.add_assoc]

/-- Under the physical node layout equations, the runtime quotient and truncated
subtractions are exactly the slot width and spectator counts. The offset is the
node start before adding the selected residue. -/
theorem compactDescriptorStage_exact (K k left right o back : ℕ) (hK : 0<K) :
    (K*(m*k))/(m*K)=k ∧
    (o+back+K*right-o-back)/K=right ∧
    (left+m*k+right)-m*k-right=left := by
  have hm : 0<m*K := Nat.mul_pos (by norm_num [m]) hK
  refine ⟨?_,?_,by omega⟩
  · rw [show K*(m*k)=k*(m*K) by ring, Nat.mul_div_cancel _ hm]
  · rw [show o+back+K*right-o-back=K*right by omega]
    exact Nat.mul_div_cancel_left right hK

end
end IntegerMultBounds.MathlibTM2.Node
