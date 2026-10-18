module

public import IntegerMultBounds.MathlibTM2.DFT.IO
public import IntegerMultBounds.MathlibTM2.DFT.Fields

/-!
# Parsing the input and printing the output

The DFT machine reads its input `encodeFixedList w (p :: ω :: as)` and writes its output
`encodeNatList X` through host registers (`DFT/IO.lean`, `DFT/Fields.lean`).

* `parse a b pr wr t` reads `gin` onto register `a` (reversed, `readIn`), moves it back onto `b`
  in order, and takes the fields of `p` and `ω` onto `pr` and `wr` through `t`. `parse_exec`:
  from empty registers, `b` ends with the entries `fieldSyms w as`, `pr` with `binSyms w p`, `wr`
  with `binSyms w ω`, and `gin` empty, in `4 N + 8 w + 14` steps for the input length `N`.
* `print_exec`: `writeOut o` on a register holding `natSyms X` reversed leaves
  `encodeNatList X` on `gout`, in `2 |natSyms X| + 2` steps.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → DPr P T Q A U)

theorem fieldSyms_cons (w x : ℕ) (l : List ℕ) :
    (fieldSyms w (x :: l) : List (Fin (A + 4))) = binSyms w x ++ separator :: fieldSyms w l := by
  simp [fieldSyms]

theorem length_fieldSyms (w : ℕ) (l : List ℕ) :
    (fieldSyms (A := A) w l).length = (encodeFixedList w l).length := by
  rw [← encodeFixedList_map, List.length_map]

/-- Read the input: `gin` onto `a` reversed, back onto `b` in order, then the first two fields
onto `pr` and `wr` through `t`. -/
def parse (a b pr wr t : Fin T) : DPr P T Q A U :=
  .seq (readIn a) (.seq (hostCode (moveR a b id))
    (.seq (hostCode (takeField b pr t)) (hostCode (takeField b wr t))))

/-- `parse`: the entries end on `b`, `p` on `pr` and `ω` on `wr`; `a` and `t` end empty and every
other stack is unchanged. -/
theorem parse_exec {a b pr wr t : Fin T} (hreg : [a, b, pr, wr, t].Nodup) (w p ω : ℕ)
    (as : List ℕ) (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = []) (hb : S.R b = [])
    (hp : S.R pr = []) (hw : S.R wr = []) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, ∃ S' : Stacks T A, v'.user = v.user ∧
      Exec body (parse a b pr wr t) (dmk v S (encodeFixedList w (p :: ω :: as)) [])
        (4 * (encodeFixedList w (p :: ω :: as)).length + 8 * w + 14) (dmk v' S' [] []) ∧
      S'.R b = fieldSyms w as ∧ S'.R pr = binSyms w p ∧ S'.R wr = binSyms w ω ∧
      S'.R a = [] ∧ S'.R t = [] ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ pr → k ≠ wr → k ≠ t → S'.R k = S.R k) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, not_false_eq_true, and_true] at hreg
  obtain ⟨⟨hab, hap, haw, hat⟩, ⟨hbp, hbw, hbt⟩, ⟨hpw, hpt⟩, hwt⟩ := hreg
  -- read `gin` onto `a`
  obtain ⟨v₁, hu₁, -, h₁⟩ := readIn_exec body a (encodeFixedList w (p :: ω :: as)) [] v S
  rw [encodeFixedList_map, ha, List.append_nil] at h₁
  set S₁ : Stacks T A :=
    { S with R := Function.update S.R a (fieldSyms w (p :: ω :: as)).reverse } with hS₁
  -- move it back onto `b`
  obtain ⟨v₂, hu₂, h₂⟩ := moveR_exec Empty.elim a b hab id v₁ S₁
  have hS₁a : S₁.R a = (fieldSyms w (p :: ω :: as)).reverse := by simp [hS₁]
  rw [hS₁a] at h₂
  set S₂ : Stacks T A :=
    { S₁ with R := movedR S₁.R a b id (fieldSyms w (p :: ω :: as)).reverse } with hS₂
  have hS₂b : S₂.R b = binSyms w p ++ separator :: fieldSyms w (ω :: as) := by
    simp [hS₂, hS₁, movedR, Ne.symm hab, hb, fieldSyms_cons]
  have hS₂t : S₂.R t = [] := by simp [hS₂, hS₁, movedR, Ne.symm hbt, Ne.symm hat, ht]
  have hS₂p : S₂.R pr = [] := by simp [hS₂, hS₁, movedR, Ne.symm hbp, Ne.symm hap, hp]
  -- take `p`
  obtain ⟨v₃, hu₃, h₃⟩ := takeField_exec Empty.elim hbp hbt hpt (separator_not_mem_binSyms w p)
    v₂ S₂ hS₂b hS₂t hS₂p
  set S₃ : Stacks T A := { S₂ with
    R := Function.update (Function.update S₂.R b (fieldSyms w (ω :: as))) pr (binSyms w p) }
    with hS₃
  have hS₃b : S₃.R b = binSyms w ω ++ separator :: fieldSyms w as := by
    simp [hS₃, hbp, fieldSyms_cons]
  have hS₃t : S₃.R t = [] := by simp [hS₃, Ne.symm hbt, Ne.symm hpt, hS₂t]
  have hS₃w : S₃.R wr = [] := by
    simp [hS₃, hS₂, hS₁, movedR, Ne.symm hbw, Ne.symm hpw, Ne.symm haw, hw]
  -- take `ω`
  obtain ⟨v₄, hu₄, h₄⟩ := takeField_exec Empty.elim hbw hbt hwt (separator_not_mem_binSyms w ω)
    v₃ S₃ hS₃b hS₃t hS₃w
  set S₄ : Stacks T A := { S₃ with
    R := Function.update (Function.update S₃.R b (fieldSyms w as)) wr (binSyms w ω) } with hS₄
  refine ⟨v₄, S₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Exec.cast (Exec.seq h₁ (Exec.seq (exec_hostCode h₂ [] [])
      (Exec.seq (exec_hostCode h₃ [] []) (exec_hostCode h₄ [] [])))) ?_ rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse, length_fieldSyms]
    simp only [binSyms, List.length_ofFn]
    ring
  · simp [hS₄, hbw]
  · simp [hS₄, hS₃, hpw, Ne.symm hbp]
  · simp [hS₄]
  · simp [hS₄, hS₃, hS₂, hS₁, movedR, haw, hab, hap]
  · simp [hS₄, Ne.symm hwt, Ne.symm hbt, hS₃t]
  · intro k hka hkb hkp hkw _
    simp [hS₄, hS₃, hS₂, hS₁, movedR, hka, hkb, hkp, hkw]
  all_goals simp [hS₄, hS₃, hS₂, hS₁]

/-- `writeOut o` on `natSyms X` reversed prints `encodeNatList X`. -/
theorem print_exec (o : Fin T) (X : List ℕ) (gi : List Γ') (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R o = (natSyms X).reverse) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (writeOut o) (dmk v S gi []) (2 * (natSyms (A := A) X).length + 2)
        (dmk v' { S with R := Function.update S.R o [] } gi (encodeNatList X)) := by
  obtain ⟨v', hu, -, h⟩ := writeOut_exec body o gi [] v S
  rw [hS, List.length_reverse, List.map_reverse, List.reverse_reverse, List.append_nil,
    natSyms_map] at h
  exact ⟨v', hu, h⟩

end IntegerMultBounds.MathlibTM2.DFT
