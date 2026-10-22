module

public import IntegerMultBounds.MathlibTM2.Node.KeyPass

/-!
# Record keying from an executed key emitter

The key emitter is a concrete program whose execution prepends one reversed key
to the accumulator and restores every other register. The record driver copies
the payload, advances the actual counters and tests the remaining source tape.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {T Q A nf : ℕ} {P U : Type}

structure KeyEmissionSpec (body : P → Pr P T Q A U) (emit : Pr P T Q A U)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (src acc : Fin T)
    (Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop)
    (key : ℕ → List (Fin (A + 4))) (cost : ℕ) : Prop where
  runs : ∀ i v S, Inv S.R i → ∃ v', v'.user = v.user ∧
    Exec body emit (mk v S) cost
      (mk v' { S with R := Function.update S.R acc ((key i).reverse ++ S.R acc) })
  digits : ∀ R i, Inv R i → ∀ f, R (cf f) = binSyms (len f) (digit len f i)
  reidx : ∀ R R' i j, Inv R i →
    (∀ f, R' (cf f) = binSyms (len f) (digit len f j)) →
    (∀ k, k ≠ src → k ≠ acc → (∀ f, k ≠ cf f) → R' k = R k) → Inv R' j

structure KeyDriverRegs (cf : Fin nf → Fin T) (src acc ctr tmp : Fin T) : Prop where
  regs : [src, acc, ctr, tmp].Nodup
  fields : Function.Injective cf
  separate : ∀ f, cf f ∉ [src, acc, ctr, tmp]

def keyRecord (emit : Pr P T Q A U) (cf : Fin nf → Fin T) (src acc ctr tmp st : Fin T) : Pr P T Q A U :=
  .seq emit
    (.seq (xferBlock (fun _ : Fin 1 => src) (fun _ => acc) ctr tmp st 1 (fun _ => 0) .done)
      (.seq (incrFields cf tmp st) (.act (peekR src))))

def keyRecordCost (emitCost B : ℕ) (len : Fin nf → ℕ) : ℕ :=
  emitCost + ((4 * B + 5) + ((4 * (∑ f, len f) + 4 * nf + 2) + 1))

/-- A single record step, with complete frame and the actual advanced counters. -/
theorem keyRecord_exec (body : P → Pr P T Q A U)
    {emit : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ}
    {src acc ctr tmp st : Fin T}
    {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop}
    {key : ℕ → List (Fin (A + 4))} {emitCost : ℕ}
    (spec : KeyEmissionSpec body emit cf len src acc Inv key emitCost)
    (regs : KeyDriverRegs cf src acc ctr tmp) (i : ℕ)
    (r rest c : List (Fin (A + 4))) (hcr : c.length = r.length)
    (v : HS T Q A U) (S : Stacks T A) (hI : Inv S.R i)
    (hsrc : S.R src = r ++ rest) (hctr : S.R ctr = c) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      v'.flag = rest.head?.isSome ∧
      Exec body (keyRecord emit cf src acc ctr tmp st) (mk v S)
        (keyRecordCost emitCost r.length len) (mk v' { S with R := R' }) ∧
      R' src = rest ∧ R' acc = (key i ++ r).reverse ++ S.R acc ∧
      Inv R' (i + 1) ∧
      ∀ k, k ≠ src → k ≠ acc → (∀ f, k ≠ cf f) → R' k = S.R k := by
  have hn := regs.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨hsa, hsc, hst⟩, ⟨hac, hat⟩, hct⟩ := hn
  have hfield (f : Fin nf) : cf f ≠ src ∧ cf f ≠ acc ∧ cf f ≠ ctr ∧ cf f ≠ tmp := by
    simpa using regs.separate f
  obtain ⟨v₁, hu₁, he₁⟩ := spec.runs i v S hI
  let R₁ := Function.update S.R acc ((key i).reverse ++ S.R acc)
  have hk₁ (k : Fin T) (hk : k ≠ acc) : R₁ k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨v₂, R₂, hu₂, _, he₂, hctr₂, htmp₂, hsrc₂, hacc₂, hoth₂⟩ :=
    xferBlock_exec body (fun _ : Fin 1 => src) (fun _ => acc) ctr tmp st 1 (fun _ => 0) .done 0
      hsc hst hct (Ne.symm hsa) hac hat c r rest v₁ { S with R := R₁ } hcr
      (by dsimp only; rw [hk₁ _ (Ne.symm hac), hctr])
      (by dsimp only; rw [hk₁ _ (Ne.symm hat), htmp])
      (by dsimp only; rw [hk₁ _ hsa, hsrc]) (Subsingleton.elim _ _)
  rw [run_done] at he₂
  dsimp only at hoth₂ hsrc₂ hctr₂ htmp₂ hacc₂
  have hk₂ (k : Fin T) (hs : k ≠ src) (ha : k ≠ acc) : R₂ k = S.R k := by
    by_cases hc : k = ctr
    · subst k; exact hctr₂.trans hctr.symm
    by_cases ht : k = tmp
    · subst k; exact htmp₂.trans htmp.symm
    rw [hoth₂ k hs hc ht ha]
    exact hk₁ k ha
  have ha : R₂ acc = (key i ++ r).reverse ++ S.R acc := by
    rw [hacc₂]
    simp [R₁, List.reverse_append, List.append_assoc]
  let v₂' := { v₂ with scan := Function.update v₁.scan st (nextC 1 (v₁.scan st)) }
  obtain ⟨v₃, R₃, hu₃, he₃, hcf₃, hoth₃⟩ := incrFields_exec body cf regs.fields tmp st
    (fun f => (hfield f).2.2.2) len i v₂' { S with R := R₂ } htmp₂
    (fun f => by
      dsimp only
      rw [hk₂ _ (hfield f).1 (hfield f).2.1]
      exact spec.digits S.R i hI f)
  dsimp only at he₃ hoth₃
  have hframe (k : Fin T) (hs : k ≠ src) (ha : k ≠ acc) (hf : ∀ f, k ≠ cf f) :
      R₃ k = S.R k := (hoth₃ k hf).trans (hk₂ k hs ha)
  let v₄ := { v₃ with flag := (R₃ src).head?.isSome }
  refine ⟨v₄, R₃, hu₃.trans (hu₂.trans hu₁), ?_, ?_, ?_, ?_,
    spec.reidx S.R R₃ i (i + 1) hI hcf₃ hframe, hframe⟩
  · change (R₃ src).head?.isSome = _
    rw [hoth₃ _ (fun f => (hfield f).1.symm), hsrc₂]
  · have he := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃
        (Exec.act (body := body) (peekR src) _)))
    exact Exec.cast he (by simp only [keyRecordCost, hcr]) rfl
  · rw [hoth₃ _ (fun f => (hfield f).1.symm), hsrc₂]
  · rw [hoth₃ _ (fun f => (hfield f).2.1.symm), ha]

/-- The full source-driven record loop, with every iteration charged. -/
theorem keyRecordLoop_exec (body : P → Pr P T Q A U)
    {emit : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ}
    {src acc ctr tmp st : Fin T}
    {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop}
    {key : ℕ → List (Fin (A + 4))} {emitCost B : ℕ}
    (spec : KeyEmissionSpec body emit cf len src acc Inv key emitCost)
    (regs : KeyDriverRegs cf src acc ctr tmp) (hB : 1 ≤ B)
    (c : List (Fin (A + 4))) (hc : c.length = B)
    (rs : List (List (Fin (A + 4)))) (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hrs : ∀ r ∈ rs, r.length = B) (hI : Inv S.R i)
    (hsrc : S.R src = rs.flatten) (hctr : S.R ctr = c) (htmp : S.R tmp = [])
    (hf : v.flag = rs.flatten.head?.isSome) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (.loop (·.flag) (keyRecord emit cf src acc ctr tmp st)) (mk v S)
        (rs.length * (keyRecordCost emitCost B len + 1) + 1) (mk v' { S with R := R' }) ∧
      R' src = [] ∧ R' acc = (keyedFrom key i rs).flatten.reverse ++ S.R acc ∧
      Inv R' (i + rs.length) ∧
      ∀ k, k ≠ src → k ≠ acc → (∀ f, k ≠ cf f) → R' k = S.R k := by
  have hn := regs.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨hsa, hsc, hst⟩, ⟨hac, hat⟩, hct⟩ := hn
  have hfield (f : Fin nf) : cf f ≠ src ∧ cf f ≠ acc ∧ cf f ≠ ctr ∧ cf f ≠ tmp := by
    simpa using regs.separate f
  induction rs generalizing i v S with
  | nil =>
    refine ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl,
      by simpa using hsrc, by simp [keyedFrom], by simpa using hI, fun _ _ _ _ => rfl⟩
  | cons r rs ih =>
    have hr := hrs r List.mem_cons_self
    obtain ⟨v₁, R₁, hu₁, hf₁, he₁, hs₁, ha₁, hI₁, hframe₁⟩ :=
      keyRecord_exec body spec regs i r rs.flatten c (hc.trans hr.symm) v S hI
        (by simpa using hsrc) hctr htmp
    obtain ⟨v₂, R₂, hu₂, he₂, hs₂, ha₂, hI₂, hframe₂⟩ := ih (i + 1) v₁ { S with R := R₁ }
      (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) hI₁ hs₁
      (by
        change R₁ ctr = c
        rw [hframe₁ ctr (Ne.symm hsc) (Ne.symm hac) (fun f => (hfield f).2.2.1.symm), hctr])
      (by
        change R₁ tmp = []
        rw [hframe₁ tmp (Ne.symm hst) (Ne.symm hat) (fun f => (hfield f).2.2.2.symm), htmp]) hf₁
    have hrne : r ≠ [] := by intro he; simp [he] at hr; omega
    have hft : v.flag = true := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hrne
      rw [hf, List.flatten_cons, hx]
      rfl
    refine ⟨v₂, R₂, hu₂.trans hu₁,
      Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft he₁ he₂)
        (by rw [hr, List.length_cons]; ring) rfl, hs₂, ?_, ?_, ?_⟩
    · rw [ha₂]
      change _ ++ R₁ acc = _
      rw [ha₁]
      simp [keyedFrom, List.flatten_cons, List.reverse_append, List.append_assoc]
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hI₂
    · intro k hs ha hc
      exact (hframe₂ k hs ha hc).trans (hframe₁ k hs ha hc)

/-- The constant key width determines the exact size moved back after keying. -/
theorem length_keyedFrom_of_length (key : ℕ → List (Fin (A + 4))) (k B : ℕ)
    (hkey : ∀ i, (key i).length = k) :
    ∀ (rs : List (List (Fin (A + 4)))) (i : ℕ), (∀ r ∈ rs, r.length = B) →
      (keyedFrom key i rs).flatten.length = rs.length * (k + B)
  | [], _, _ => by simp [keyedFrom]
  | r :: rs, i, hrs => by
    rw [keyedFrom, List.flatten_cons, List.length_append, List.length_append, hkey,
      hrs r List.mem_cons_self, length_keyedFrom_of_length key k B hkey rs (i + 1)
        (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))]
    simp only [List.length_cons]
    ring

def keyStream (emit : Pr P T Q A U) (cf : Fin nf → Fin T) (src acc ctr tmp st : Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (keyRecord emit cf src acc ctr tmp st))
      (.seq (moveR acc src id) (resetFields cf tmp)))

/-- Complete keying: actual record loop, stream restoration and counter reset. -/
theorem keyStream_exec (body : P → Pr P T Q A U)
    {emit : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ}
    {src acc ctr tmp st : Fin T}
    {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop}
    {key : ℕ → List (Fin (A + 4))} {emitCost k B : ℕ}
    (spec : KeyEmissionSpec body emit cf len src acc Inv key emitCost)
    (regs : KeyDriverRegs cf src acc ctr tmp) (hB : 1 ≤ B) (hkey : ∀ i, (key i).length = k)
    (l : List (List (Fin (A + 4)))) (hlen : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hI : Inv S.R 0)
    (hsrc : S.R src = l.flatten) (hacc : S.R acc = []) (hctr : (S.R ctr).length = B)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (keyStream emit cf src acc ctr tmp st) (mk v S)
        (1 + (l.length * (keyRecordCost emitCost B len + 1) + 1) +
          (2 * (l.length * (k + B)) + 2) + (4 * (∑ f, len f) + 4 * nf + 1))
        (mk v' { S with R := Function.update S.R src (keyedFrom key 0 l).flatten }) := by
  have hn := regs.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨hsa, hsc, hst⟩, ⟨hac, hat⟩, hct⟩ := hn
  have hfield (f : Fin nf) : cf f ≠ src ∧ cf f ≠ acc ∧ cf f ≠ ctr ∧ cf f ≠ tmp := by
    simpa using regs.separate f
  obtain ⟨v₁, R₁, hu₁, he₁, hs₁, ha₁, hI₁, hoth₁⟩ := keyRecordLoop_exec body spec regs hB
    (S.R ctr) hctr l 0 { v with flag := (S.R src).head?.isSome } S hlen hI hsrc rfl htmp
    (by rw [hsrc])
  rw [hacc, List.append_nil] at ha₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc src (Ne.symm hsa) id v₁ { S with R := R₁ }
  let R₂ := movedR R₁ acc src id (R₁ acc)
  have hs₂ : R₂ src = (keyedFrom key 0 l).flatten := by simp [R₂, movedR, ha₁, hs₁]
  have ha₂ : R₂ acc = [] := by simp [R₂, movedR, Ne.symm hsa]
  have hk₂ (j : Fin T) (hs : j ≠ src) (ha : j ≠ acc) : R₂ j = R₁ j := by simp [R₂, movedR, hs, ha]
  obtain ⟨v₃, R₃, hu₃, he₃, hcf₃, hoth₃⟩ := resetFields_exec body cf regs.fields tmp
    (fun f => (hfield f).2.2.2) len v₂ { S with R := R₂ }
    (by
      change R₂ tmp = []
      rw [hk₂ _ (Ne.symm hst) (Ne.symm hat),
        hoth₁ _ (Ne.symm hst) (Ne.symm hat) (fun f => (hfield f).2.2.2.symm), htmp])
    (fun f => by
      change (R₂ (cf f)).length = _
      rw [hk₂ _ (hfield f).1 (hfield f).2.1, spec.digits R₁ _ hI₁ f]
      simp)
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.cast
    (Exec.seq (Exec.act (body := body) (peekR src) (mk v S))
      (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · change _ + (_ + (2 * (R₁ acc).length + 2 + _)) = _
    rw [ha₁, List.length_reverse, length_keyedFrom_of_length key k B hkey l 0 hlen]
    ring
  · congr 2
    funext j
    by_cases hf : ∃ f, j = cf f
    · obtain ⟨f, rfl⟩ := hf
      rw [hcf₃ f, Function.update_of_ne (hfield f).1, spec.digits S.R 0 hI f]
      simp [digit]
    simp only [not_exists] at hf
    rw [hoth₃ j hf]
    change R₂ j = _
    by_cases hs : j = src
    · subst j; rw [hs₂, Function.update_self]
    by_cases ha : j = acc
    · subst j; rw [ha₂, Function.update_of_ne hs, hacc]
    rw [hk₂ j hs ha, hoth₁ j hs ha hf, Function.update_of_ne hs]

end IntegerMultBounds.MathlibTM2.Routing
