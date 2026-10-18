module

public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
public import IntegerMultBounds.MathlibTM2.Node.Phase

/-!
# Zero arrays of a wire's shape

The T16 node uses eight private centres as dirty scratch: its program is correct for any centre
contents, but the tape passes on a centre need a stream of the wire's shape. `zeroFill` reads a
source register once with the Gaussian automaton of the copy-and-zero matrix `copyZeroG` (output
`0` is the input, output `1` is zero), writing the copy onto a spare register and the zero
coefficients onto the target, and moves the copy back.

* `encZ_zero`: the zero array's stream is a constant run of the zero pair symbol.
* `zeroFill_exec`: the source keeps its stream, the target ends with the stream of the zero array of
  the same shape, and every other register ends as it started.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

/-! ### Zero streams -/

theorem coeffSyms_zero (A W : ℕ) :
    coeffSyms A W (0 : GR W) = List.replicate W (pairSym A false false) := by
  simp [coeffSyms, List.ofFn_const]

theorem flatMap_zeros (A W : ℕ) (l : List (GR W)) (hl : ∀ z ∈ l, z = 0) :
    l.flatMap (coeffSyms A W) = List.replicate (l.length * W) (pairSym A false false) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [List.flatMap_cons, hl z List.mem_cons_self, coeffSyms_zero,
      ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)), List.length_cons, ← List.replicate_add]
    congr 1
    ring

/-- The zero array's stream is a constant run of the zero pair symbol. -/
theorem encZ_zero (A w : ℕ) {R r n : ℕ} :
    encZ A w (0 : ZArr (Fin R × Fin r) n) =
      List.replicate (R * 2 ^ n * r * w) (pairSym A false false) := by
  rw [encZ, flatMap_zeros, length_coeffList]
  intro z hz
  rw [coeffList_eq_map, List.mem_map] at hz
  obtain ⟨p, _, rfl⟩ := hz
  simp [red]

/-- A list of length `n` is the `ofFn` of its entries. -/
theorem ofFn_getElem_length {α : Type*} {n : ℕ} (L : List α) (h : L.length = n) :
    List.ofFn (fun c : Fin n => L[(c : ℕ)]'(by rw [h]; exact c.isLt)) = L := by
  apply List.ext_getElem (by simp [h])
  intro t _ _
  simp

/-! ### The copy-and-zero matrix -/

/-- Output `0` is the input, output `1` is zero. -/
def copyZeroG : Fin 2 → Fin 1 → ℤ × ℤ := ![![(1, 0)], ![(0, 0)]]

theorem glin_copyZero_zero {W : ℕ} (zs : Fin 1 → GR W) : glin copyZeroG zs 0 = zs 0 := by
  simp [glin, copyZeroG]

theorem glin_copyZero_one {W : ℕ} (zs : Fin 1 → GR W) : glin copyZeroG zs 1 = 0 := by
  simp [glin, copyZeroG]

/-! ### The fill -/

section Exec

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Copy `src` through `cpy` while writing a zero array of the same shape onto `dst`. -/
def zeroFill (src cpy dst st ctr tmp : Fin T) : Pr P T Q A U :=
  .seq (autoWords (fun _ : Fin 1 => src) ![cpy, dst] st ctr tmp (gaussAuto A copyZeroG 1 false))
    (moveR cpy src id)

/-- **The zero fill.** The source keeps its stream, the target ends holding the stream of the zero
array of the same shape, and every other register ends as it started. -/
theorem zeroFill_exec {src cpy dst st ctr tmp : Fin T}
    (h : AutoLayout (fun _ : Fin 1 => src) ![cpy, dst] st ctr tmp) (hA : 77 ≤ A)
    {R r n w : ℕ} (hw : 1 ≤ w) {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = w)
    (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A) (hctr : S.R ctr = ctrs)
    (htmp : S.R tmp = []) (hcpy : S.R cpy = []) (hdst : S.R dst = [])
    (hsrc : S.R src = encZ A w Z) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ R * 2 ^ n * r * (7 * w + 6) + 4 ∧
      Exec body (zeroFill src cpy dst st ctr tmp) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (encZ A w (0 : ZArr (Fin R × Fin r) n)) }) := by
  have hsc : src ≠ cpy := h.ins_outs 0 0
  have hsd : src ≠ dst := h.ins_outs 0 1
  have hcd : cpy ≠ dst := by
    intro e
    have h01 := h.outs_inj (a₁ := 0) (a₂ := 1) (by simpa using e)
    exact absurd h01 (by decide)
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, he₁, hi₁, ho₁, hl₁, hins, houts, hoth⟩ :=
    gaussAuto_exec_list body h (B := 1) (g := copyZeroG) (by omega)
      (fun j => by fin_cases j <;> simp [copyZeroG]) (by norm_num; omega) false hw hctrs
      (fun _ => coeffList w Z) (fun _ => length_coeffList Z) v S hctr htmp (fun _ => hsrc)
  have hcopy : S₁.R cpy = (encZ A w Z).reverse := by
    have := houts 0
    simp only [Matrix.cons_val_zero, glin_copyZero_zero, swapGR_false] at this
    rw [this, hcpy, List.append_nil, ofFn_getElem_length _ (length_coeffList Z)]
    rfl
  have hzero : S₁.R dst = encZ A w (0 : ZArr (Fin R × Fin r) n) := by
    have := houts 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
      glin_copyZero_one] at this
    rw [this, hdst, List.append_nil, flatMap_zeros A w _ (by simp), encZ_zero, List.length_ofFn,
      List.reverse_replicate]
  have hS₁ : S₁ = { S with R := S₁.R } := Stacks.ext hi₁ ho₁ hl₁ rfl
  obtain ⟨v₂, hu₂, he₂⟩ := Host.moveR_exec body cpy src hsc.symm id v₁ S₁
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  · rw [hcopy, List.length_reverse, Node.length_encZ]
    nlinarith
  · rw [hS₁]
    congr 2
    funext x
    simp only [movedR, List.map_id]
    by_cases hx1 : x = src
    · subst hx1
      rw [Function.update_self, Function.update_of_ne hsd, hcopy, List.reverse_reverse,
        hins 0, List.append_nil, hsrc]
    rw [Function.update_of_ne hx1]
    by_cases hx2 : x = cpy
    · subst hx2
      rw [Function.update_self, Function.update_of_ne hcd, hcpy]
    rw [Function.update_of_ne hx2]
    by_cases hx3 : x = dst
    · subst hx3
      rw [Function.update_self, hzero]
    rw [Function.update_of_ne hx3]
    apply hoth
    · rintro ⟨i, rfl⟩
      exact hx1 rfl
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact hx2 rfl
      · exact hx3 rfl

end Exec

end IntegerMultBounds.MathlibTM2.Layer
