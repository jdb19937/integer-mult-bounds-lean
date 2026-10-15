module

public import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorPadding

/-! Runtime row and payload arithmetic and fixed-arity slot numbering. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {T Q A : ℕ} {U P : Type}

/-- A compiled constant is used only for the globally fixed arity. -/
def compactDescriptorConst (c : ℕ) (dst : Fin T) : Pr P T Q A U :=
  .act (pushN dst (fun _ => tick) c .done)

lemma compactDescriptorConst_runs (body : P → Pr P T Q A U)
    (c : ℕ) (dst : Fin T) (R : Fin T → List (Fin (A+4))) :
    LayRuns body (compactDescriptorConst c dst) R
      (Function.update R dst (List.replicate c tick ++ R dst)) 1 := by
  apply lr_of_exec body
  intro v S hS
  subst hS
  refine ⟨v,rfl,?_⟩
  have h := Exec.act (body:=body) (pushN dst (fun _ => tick) c .done) (mk v S)
  rw [pushN_run,run_done] at h
  exact h

/-- Roles: total address bits, absorbed low bits, shape bits, outside rows,
result rows, exponent scratch, two scan scratch tapes. -/
def compactDescriptorRows (e : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (ucopy (e 0) (e 5) (e 6)) <|
  .seq (usub (e 1) (e 5) (e 6)) <|
  .seq (usub (e 2) (e 5) (e 6)) <|
  .seq (ucopy (e 3) (e 4) (e 6)) <|
  .seq (upow2 (e 5) (e 4) (e 6) (e 7)) (uclear (e 5))

def compactDescriptorRowsCost (n o bits rows : ℕ) :=
  (4*n+4)+(4*o+4)+(4*bits+4)+(4*rows+4)+
  (4*(2^(n-o-bits)*rows)+9*(n-o-bits)+4)+(2*(n-o-bits)+2)

theorem compactDescriptorRows_runs (body : P → Pr P T Q A U)
    (e : Fin 8 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4)))
    (hz : ∀ i : Fin 8, 4 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorRows e) R
      (Function.update R (e 4) (List.replicate
        (2^((R (e 0)).length-(R (e 1)).length-(R (e 2)).length)*(R (e 3)).length) tick))
      (compactDescriptorRowsCost (R (e 0)).length (R (e 1)).length
        (R (e 2)).length (R (e 3)).length) := by
  have h4 := hz 4 (by decide); have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide); have h7 := hz 7 (by decide)
  have hd : [e 5,e 4,e 6,e 7].Nodup := by
    simpa using (show ([5,4,6,7] : List (Fin 8)).Nodup by decide).map he
  refine lr_weaken body
    ((lr_ucopy body (R:=R) (a:=e 0) (b:=e 5) (t:=e 6)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) h6).seq <|
    (lr_usub body (a:=e 1) (b:=e 5) (t:=e 6)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h6])).seq <|
    (lr_usub body (a:=e 2) (b:=e 5) (t:=e 6)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h6])).seq <|
    (lr_ucopy body (a:=e 3) (b:=e 4) (t:=e 6)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h6])).seq <|
    (lr_upow2 body hd (by simp [he.eq_iff,h6]) (by simp [he.eq_iff,h7])).seq <|
    lr_uclear body (e 5)) ?_ ?_
  · funext z
    by_cases hz4 : z=e 4
    · subst z; simp [he.eq_iff,h4,h5,List.drop_replicate,List.flatMap_replicate,Nat.mul_comm]
    by_cases hz5 : z=e 5
    · subst z; simp [he.eq_iff,h5]
    simp [Function.update_of_ne,hz4,hz5]
  · simp [he.eq_iff,h4,h5,List.drop_replicate,compactDescriptorRowsCost,Nat.add_assoc]

/-- Roles: absorbed low bits, coefficient count, coefficient width, payload
result, product scratch, two scan scratch tapes. -/
def compactDescriptorPayload (e : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (synMulR (e 1) (e 2) (e 4) (e 5) (e 6)) <|
  .seq (umul 3 (e 4) (e 3) (e 5)) <|
  .seq (upow2 (e 0) (e 3) (e 5) (e 6)) (uclear (e 4))

def compactDescriptorPayloadCost (o r w : ℕ) :=
  synMulRCost r w+(4*(r*w)+4)+(4*(2^o*(3*(r*w)))+9*o+4)+(2*(r*w)+2)

theorem compactDescriptorPayload_runs (body : P → Pr P T Q A U)
    (e : Fin 7 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4)))
    (hz : ∀ i : Fin 7, 3 ≤ i.val → R (e i)=[]) :
    LayRuns body (compactDescriptorPayload e) R
      (Function.update R (e 3) (List.replicate
        (2^(R (e 0)).length*(3*((R (e 1)).length*(R (e 2)).length))) tick))
      (compactDescriptorPayloadCost (R (e 0)).length (R (e 1)).length (R (e 2)).length) := by
  have h3 := hz 3 (by decide); have h4 := hz 4 (by decide)
  have h5 := hz 5 (by decide); have h6 := hz 6 (by decide)
  have hm : [e 1,e 2,e 4,e 5,e 6].Nodup := by
    simpa using (show ([1,2,4,5,6] : List (Fin 7)).Nodup by decide).map he
  have hp : [e 0,e 3,e 5,e 6].Nodup := by
    simpa using (show ([0,3,5,6] : List (Fin 7)).Nodup by decide).map he
  refine lr_weaken body
    ((lr_synMulR body (R:=R) hm h5 h6).seq <|
    (lr_umul body 3 (a:=e 4) (b:=e 3) (t:=e 5)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h5])).seq <|
    (lr_upow2 body hp (by simp [he.eq_iff,h5]) (by simp [he.eq_iff,h6])).seq <|
    lr_uclear body (e 4)) ?_ ?_
  · funext z
    by_cases hz3 : z=e 3
    · subst z; simp [he.eq_iff,h3,h4,List.flatMap_replicate,Nat.mul_comm]
    by_cases hz4 : z=e 4
    · subst z; simp [he.eq_iff,h4]
    simp [Function.update_of_ne,hz3,hz4]
  · simp [he.eq_iff,h3,h4,compactDescriptorPayloadCost,Nat.add_assoc]

/-- Roles: runtime forward index, reversed index, scratch. -/
def compactDescriptorReverse (e : Fin 3 → Fin T) : Pr P T Q A U :=
  .seq (compactDescriptorConst (m-1) (e 1)) (usub (e 0) (e 1) (e 2))

lemma compactDescriptorReverse_runs (body : P → Pr P T Q A U)
    (e : Fin 3 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (h1 : R (e 1)=[]) (h2 : R (e 2)=[]) :
    LayRuns body (compactDescriptorReverse e) R
      (Function.update R (e 1) (List.replicate (m-1-(R (e 0)).length) tick))
      (1+(4*(R (e 0)).length+4)) := by
  refine lr_weaken body ((compactDescriptorConst_runs body (m-1) (e 1) R).seq
    (lr_usub body (a:=e 0) (b:=e 1) (t:=e 2)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (by simp [he.eq_iff,h2]))) ?_ ?_
  · simp [he.eq_iff,h1,List.drop_replicate,Function.update_idem]
  · simp [he.eq_iff]

end
end IntegerMultBounds.MathlibTM2.Node
