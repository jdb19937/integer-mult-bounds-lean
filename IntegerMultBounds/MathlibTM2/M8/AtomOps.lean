module

public import IntegerMultBounds.MathlibTM2.M8.TwistedProgram
public import IntegerMultBounds.Networks.AffineFieldCoordinates

/-!
# Atom operations as ordinary coordinate operations

A coordinate that carries `f` atoms is `f` ordinary coordinates of the machine: the vector
`x : Fin n → Fin f → R` is laid out as `refine x : Fin (n * f) → R`, coordinate-major, so atom
`l` of coordinate `t` is coordinate `t f + l` (`at`). The atomwise operations of the stage-2 field
programs (`AtomOp`) are a scaling, a shift and a reversed shift `x_t ← x_t + c σ(x_k)`, which reads
the atoms of `x_k` in reverse order. Each is the run of one ordinary operation per atom level
(`levels`, `refined_run`), legal when the control coordinate precedes the target
(`refined_legal`): every atom of `x_k` precedes every atom of `x_t`.

`atomExpand` is `AffineFieldCoordinates.expand` with the head read reversed. On the `H ++ D`
vector it runs as the twisted field program over the atom ring `Fin f → R` with scalar
coefficients (`atom_segment_run`): `TwistedProgram.twRun` at `σ = atomRev`. So a nonrecursive
segment of the network, run twisted on atom fields, is a run of ordinary operations on `2 m f`
coordinates, `f` per field operation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.AtomOps

open IntegerMultBounds.Networks
open AffineFieldCoordinates (hIndex dIndex embed)

variable {n f : ℕ} {R : Type*} [CommRing R]

/-- Atom `l` of coordinate `t`. -/
def «at» (t : Fin n) (l : Fin f) : Fin (n * f) := finProdFinEquiv (t, l)

/-- The atom vector as ordinary coordinates, coordinate-major. -/
def refine (x : Fin n → Fin f → R) : Fin (n * f) → R :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

omit [CommRing R] in
@[simp] theorem refine_at (x : Fin n → Fin f → R) (t : Fin n) (l : Fin f) :
    refine x («at» t l) = x t l := by
  simp [refine, «at»]

omit [CommRing R] in
theorem refine_update (x : Fin n → Fin f → R) (t : Fin n) (l : Fin f) (z : R) :
    Function.update (refine x) («at» t l) z =
      refine (Function.update x t (Function.update (x t) l z)) := by
  funext k
  obtain ⟨⟨k₁, k₂⟩, rfl⟩ := finProdFinEquiv.surjective k
  change Function.update (refine x) («at» t l) z («at» k₁ k₂) =
    refine (Function.update x t (Function.update (x t) l z)) («at» k₁ k₂)
  rw [refine_at]
  by_cases h₁ : k₁ = t
  · subst h₁
    by_cases h₂ : k₂ = l
    · subst h₂; simp
    · have hne : «at» k₁ k₂ ≠ «at» k₁ l := fun h => h₂ (by simp [«at»] at h; exact h)
      simp [Function.update_of_ne hne, Function.update_of_ne h₂]
  · have hne : «at» k₁ k₂ ≠ «at» t l := fun h => h₁ (by simp [«at»] at h; exact h.1)
    simp [Function.update_of_ne hne, Function.update_of_ne h₁]

omit [CommRing R] in
theorem at_lt {k t : Fin n} (h : k < t) (l l' : Fin f) : «at» k l' < «at» t l := by
  rw [Fin.lt_def]
  simp only [«at», finProdFinEquiv_apply_val]
  have hl := l'.isLt
  have : f * (k : ℕ) + f ≤ f * t := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left f h
  omega

/-! ### Level runs -/

/-- One level step: atom `l` of coordinate `t` takes the value `v l x`. -/
def step (t : Fin n) (v : Fin f → (Fin n → Fin f → R) → R) (l : Fin f)
    (x : Fin n → Fin f → R) : Fin n → Fin f → R :=
  Function.update x t (Function.update (x t) l (v l x))

omit [CommRing R] in
/-- Steps at distinct levels whose values read only other coordinates and their own atom run
as one simultaneous update of coordinate `t`. -/
theorem foldl_steps (t : Fin n) (v : Fin f → (Fin n → Fin f → R) → R)
    (hv : ∀ l x y, (∀ k, k ≠ t → x k = y k) → x t l = y t l → v l x = v l y) :
    ∀ (ls : List (Fin f)), ls.Nodup → ∀ x,
      ls.foldl (fun x l => step t v l x) x =
        Function.update x t (fun l => if l ∈ ls then v l x else x t l)
  | [], _, x => by simp
  | l :: ls, hnd, x => by
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, foldl_steps t v hv ls hnd.2]
    funext k a
    by_cases hk : k = t
    · subst hk
      simp only [Function.update_self, step, List.mem_cons]
      by_cases ha : a = l
      · subst ha
        simp only [hnd.1, ite_false, Function.update_self, true_or, ite_true]
      · have hy : ∀ b, b ∈ ls → v b (step k v l x) = v b x := fun b hb =>
          hv b _ _ (fun j hj => by simp [step, Function.update_of_ne hj]) (by
            have hbl : b ≠ l := fun h => hnd.1 (h ▸ hb)
            simp [step, Function.update_of_ne hbl])
        by_cases hb : a ∈ ls
        · have := hy a hb
          simp only [step] at this
          simp [hb, ha, this]
        · simp [hb, ha]
    · simp [step, Function.update_of_ne hk]

/-- The ordinary operations of a step list, one per atom level in order. -/
def levels (g : Fin f → OrderedAffine.Op (Fin (n * f)) R) : List (OrderedAffine.Op (Fin (n * f)) R) :=
  (List.finRange f).map g

theorem run_levels (g : Fin f → OrderedAffine.Op (Fin (n * f)) R) (t : Fin n)
    (v : Fin f → (Fin n → Fin f → R) → R)
    (hv : ∀ l x y, (∀ k, k ≠ t → x k = y k) → x t l = y t l → v l x = v l y)
    (hg : ∀ l x, OrderedAffine.execute (g l) (refine x) = refine (step t v l x))
    (x : Fin n → Fin f → R) :
    OrderedAffine.run (levels g) (refine x) = refine (Function.update x t (fun l => v l x)) := by
  have h : ∀ (ls : List (Fin f)) x, OrderedAffine.run (ls.map g) (refine x) =
      refine (ls.foldl (fun x l => step t v l x) x) := by
    intro ls
    induction ls with
    | nil => intro x; rfl
    | cons l ls ih =>
      intro x
      change OrderedAffine.run (ls.map g) (OrderedAffine.execute (g l) (refine x)) = _
      rw [hg, ih]
      rfl
  rw [levels, h, foldl_steps t v hv _ (List.nodup_finRange f)]
  simp

/-! ### Atom operations -/

/-- The atomwise operations: scaling, shift, and the shift with the control's atoms reversed. -/
inductive AtomOp (n : ℕ) (R : Type*)
  | scale (t : Fin n) (c : R)
  | shift (t k : Fin n) (c : R)
  | revShift (t k : Fin n) (c : R)

/-- The atomwise action. -/
def atomExecute : AtomOp n R → (Fin n → Fin f → R) → Fin n → Fin f → R
  | .scale t c, x => Function.update x t (fun l => c * x t l)
  | .shift t k c, x => Function.update x t (fun l => x t l + c * x k l)
  | .revShift t k c, x => Function.update x t (fun l => x t l + c * x k l.rev)

/-- An atom operation as one ordinary operation per level. -/
def refined : AtomOp n R → List (OrderedAffine.Op (Fin (n * f)) R)
  | .scale t c => levels fun l => .scale («at» t l) c
  | .shift t k c => levels fun l => .shift («at» t l) («at» k l) c
  | .revShift t k c => levels fun l => .shift («at» t l) («at» k l.rev) c

/-- The shifts read another coordinate. -/
def Distinct : AtomOp n R → Prop
  | .scale _ _ => True
  | .shift t k _ => k ≠ t
  | .revShift t k _ => k ≠ t

theorem refined_run (op : AtomOp n R) (hop : Distinct op) (x : Fin n → Fin f → R) :
    OrderedAffine.run (refined op) (refine x) = refine (atomExecute op x) := by
  cases op with
  | scale t c =>
    refine run_levels _ t (fun l x => c * x t l) (fun l x y _ h => by rw [h]) (fun l x => ?_) x
    simp [OrderedAffine.execute, refine_update, step]
  | shift t k c =>
    refine run_levels _ t (fun l x => x t l + c * x k l)
      (fun l x y hk h => by rw [h, hk k hop]) (fun l x => ?_) x
    simp [OrderedAffine.execute, refine_update, step]
  | revShift t k c =>
    refine run_levels _ t (fun l x => x t l + c * x k l.rev)
      (fun l x y hk h => by rw [h, hk k hop]) (fun l x => ?_) x
    simp [OrderedAffine.execute, refine_update, step]

/-- Legal atom operations: unit scalings, and shifts whose control precedes the target. -/
def AtomLegal : AtomOp n R → Prop
  | .scale _ c => IsUnit c
  | .shift t k _ => k < t
  | .revShift t k _ => k < t

theorem refined_legal (op : AtomOp n R) (hop : AtomLegal op) :
    ∀ o ∈ refined (f := f) op, OrderedAffine.Legal o := by
  intro o ho
  cases op with
  | scale t c =>
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ho
    exact hop
  | shift t k c =>
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ho
    exact at_lt hop l l
  | revShift t k c =>
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ho
    exact at_lt hop l l.rev

/-! ### Field programs on atom fields -/

/-- `AffineFieldCoordinates.expand` with the head read in reverse atom order. -/
def atomExpand {d : ℕ} : AffineFieldProgram.Op (Fin d) R → List (AtomOp (d + d) R)
  | .affineH (.scale i c) => [.scale (hIndex i) c]
  | .affineH (.shift i j c) => [.shift (hIndex i) (hIndex j) c]
  | .affineD (.scale i c) => [.scale (dIndex i) c]
  | .affineD (.shift i j c) => [.shift (dIndex i) (dIndex j) c]
  | .addToD i j => [.revShift (dIndex j) (hIndex i) 1]
  | .subFromD i j => [.scale (dIndex j) (-1), .revShift (dIndex j) (hIndex i) 1]
  | .interchange _ _ => []

/-- The run of a list of atom operations. -/
def atomRun (ops : List (AtomOp n R)) (x : Fin n → Fin f → R) : Fin n → Fin f → R :=
  ops.foldl (fun x op => atomExecute op x) x

theorem atomRun_append (p q : List (AtomOp n R)) (x : Fin n → Fin f → R) :
    atomRun (p ++ q) x = atomRun q (atomRun p x) := List.foldl_append

/-- The refined run of a list of distinct atom operations. -/
theorem refined_atomRun : ∀ (ops : List (AtomOp n R)), (∀ op ∈ ops, Distinct op) →
    ∀ x : Fin n → Fin f → R,
      OrderedAffine.run (ops.flatMap refined) (refine x) = refine (atomRun ops x)
  | [], _, _ => rfl
  | op :: ops, h, x => by
    rw [List.flatMap_cons]
    change OrderedAffine.run (refined op ++ ops.flatMap refined) (refine x) =
      refine (atomRun ops (atomExecute op x))
    rw [show OrderedAffine.run (refined op ++ ops.flatMap refined) (refine x) =
      OrderedAffine.run (ops.flatMap refined) (OrderedAffine.run (refined op) (refine x)) from
      List.foldl_append, refined_run op (h op (by simp)),
      refined_atomRun ops (fun o ho => h o (by simp [ho]))]

section Fields

variable {d : ℕ}

omit [CommRing R] in
theorem embed_update_h (h e : Fin d → Fin f → R) (i : Fin d) (z : Fin f → R) :
    embed (Function.update h i z, e) = Function.update (embed (h, e)) (hIndex i) z := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · by_cases hk : k = i
    · subst hk; simp
    · have : hIndex (d := d) k ≠ hIndex i := fun h => hk (Fin.castAdd_injective _ _ h)
      rw [Function.update_of_ne this, AffineFieldCoordinates.embed_h, AffineFieldCoordinates.embed_h]
      exact Function.update_of_ne hk _ _
  · have : dIndex (d := d) k ≠ hIndex i := (AffineFieldCoordinates.h_before_d i k).ne'
    rw [Function.update_of_ne this, AffineFieldCoordinates.embed_d, AffineFieldCoordinates.embed_d]

omit [CommRing R] in
theorem embed_update_d (h e : Fin d → Fin f → R) (i : Fin d) (z : Fin f → R) :
    embed (h, Function.update e i z) = Function.update (embed (h, e)) (dIndex i) z := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · have : hIndex (d := d) k ≠ dIndex i := (AffineFieldCoordinates.h_before_d k i).ne
    rw [Function.update_of_ne this, AffineFieldCoordinates.embed_h, AffineFieldCoordinates.embed_h]
  · by_cases hk : k = i
    · subst hk
      rw [AffineFieldCoordinates.embed_d, Function.update_self]
      exact Function.update_self _ _ _
    · have : dIndex (d := d) k ≠ dIndex i := fun h => hk (Fin.natAdd_injective _ _ h)
      rw [Function.update_of_ne this, AffineFieldCoordinates.embed_d, AffineFieldCoordinates.embed_d]
      exact Function.update_of_ne hk _ _

/-- The scalars of the atom ring. -/
abbrev scalar : R → (Fin f → R) := algebraMap R (Fin f → R)

/-- **One field operation on atom fields.** A nonrecursive operation with scalar coefficients,
run twisted by the atom reversal, is the run of its atom operations. -/
theorem atomExpand_run (op : AffineFieldProgram.Op (Fin d) R)
    (hn : AffineFieldCoordinates.Nonrecursive op) (s : Swap.Shear.State (Fin d) (Fin f → R)) :
    atomRun (atomExpand op) (embed s) =
      embed (TwistedProgram.twExecute (TwistedExchange.atomRev f)
        (AffineFieldProgram.mapOp scalar op) s) := by
  obtain ⟨h, e⟩ := s
  cases op with
  | affineH op =>
    cases op with
    | scale i c =>
      simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
        AffineFieldProgram.mapOp, OrderedAffine.mapOp, TwistedProgram.twExecute,
        OrderedAffine.execute, embed_update_h, AffineFieldCoordinates.embed_h]
      congr 1
    | shift i j c =>
      simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
        AffineFieldProgram.mapOp, OrderedAffine.mapOp, TwistedProgram.twExecute,
        OrderedAffine.execute, embed_update_h, AffineFieldCoordinates.embed_h]
      congr 1
  | affineD op =>
    cases op with
    | scale i c =>
      simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
        AffineFieldProgram.mapOp, OrderedAffine.mapOp, TwistedProgram.twExecute,
        OrderedAffine.execute, embed_update_d, AffineFieldCoordinates.embed_d]
      congr 1
    | shift i j c =>
      simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
        AffineFieldProgram.mapOp, OrderedAffine.mapOp, TwistedProgram.twExecute,
        OrderedAffine.execute, embed_update_d, AffineFieldCoordinates.embed_d]
      congr 1
  | addToD i j =>
    simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
      AffineFieldProgram.mapOp, TwistedProgram.twExecute, embed_update_d,
      AffineFieldCoordinates.embed_d, AffineFieldCoordinates.embed_h]
    congr 1
    funext l
    simp
  | subFromD i j =>
    simp only [atomExpand, atomRun, List.foldl_cons, List.foldl_nil, atomExecute,
      AffineFieldProgram.mapOp, TwistedProgram.twExecute, embed_update_d,
      AffineFieldCoordinates.embed_d, Function.update_self,
      Function.update_idem]
    congr 1
    funext l
    simp only [TwistedExchange.atomRev_apply, Pi.sub_apply]
    have : hIndex (d := d) i ≠ dIndex j := (AffineFieldCoordinates.h_before_d i j).ne
    rw [Function.update_of_ne this, AffineFieldCoordinates.embed_h]
    ring
  | interchange i j => exact hn.elim

/-- **A segment on atom fields.** A nonrecursive segment with scalar coefficients, run twisted by
the atom reversal, is the run of its atom operations. -/
theorem atom_segment_run : ∀ (ops : List (AffineFieldProgram.Op (Fin d) R)),
    (∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op) →
    ∀ s : Swap.Shear.State (Fin d) (Fin f → R),
      atomRun (ops.flatMap atomExpand) (embed s) =
        embed (TwistedProgram.twRun (TwistedExchange.atomRev f)
          (ops.map (AffineFieldProgram.mapOp scalar)) s)
  | [], _, _ => rfl
  | op :: ops, h, s => by
    rw [List.flatMap_cons, atomRun_append, atomExpand_run op (h op (by simp)),
      atom_segment_run ops (fun o ho => h o (by simp [ho]))]
    rfl

/-- Legal field operations expand to distinct, legal atom operations. -/
theorem atomExpand_legal (op : AffineFieldProgram.Op (Fin d) R) (hl : AffineFieldProgram.Legal op) :
    ∀ a ∈ atomExpand op, AtomLegal a ∧ Distinct a := by
  intro a ha
  cases op with
  | affineH op =>
    cases op with
    | scale i c =>
      simp only [atomExpand, List.mem_singleton] at ha; subst ha
      exact ⟨hl, trivial⟩
    | shift i j c =>
      simp only [atomExpand, List.mem_singleton] at ha; subst ha
      have : hIndex (d := d) j < hIndex i := hl
      exact ⟨this, this.ne⟩
  | affineD op =>
    cases op with
    | scale i c =>
      simp only [atomExpand, List.mem_singleton] at ha; subst ha
      exact ⟨hl, trivial⟩
    | shift i j c =>
      simp only [atomExpand, List.mem_singleton] at ha; subst ha
      have : dIndex (d := d) j < dIndex i := by
        change d + (j : ℕ) < d + i
        have : (j : ℕ) < i := hl
        omega
      exact ⟨this, this.ne⟩
  | addToD i j =>
    simp only [atomExpand, List.mem_singleton] at ha; subst ha
    exact ⟨AffineFieldCoordinates.h_before_d i j, (AffineFieldCoordinates.h_before_d i j).ne⟩
  | subFromD i j =>
    simp only [atomExpand, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨isUnit_one.neg, trivial⟩
    · exact ⟨AffineFieldCoordinates.h_before_d i j, (AffineFieldCoordinates.h_before_d i j).ne⟩
  | interchange i j => simp [atomExpand] at ha

end Fields

end IntegerMultBounds.MathlibTM2.M8.AtomOps
