module

public import IntegerMultBounds.MathlibTM2.Phases

/-!
# Correctness of the bridge program

`prepare` turns Mathlib's encoding of `(A, B)` into `x # y` on tape 0, where `x` and `y` are the
most-significant-first binary words of `A` and `B` padded to a common length `n ≥ 1`. `finish`
turns a halting configuration with a correct output word into Mathlib's encoding of `A * B` on the
output stack, with every other stack empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Computability

variable {t q a : ℕ}

set_option linter.unusedSimpArgs false

/-- Stacks holding only the input. -/
def inputStacks (l : List (Bool ⊕ Bool)) : Stacks t a :=
  ⟨l, [], [], [], [], [], fun _ => [], fun _ => []⟩

/-- Stacks holding only the word `w` on the right stack of tape 0. -/
def tapeStacks (M : Program t q a) (w : List (Fin (a + 4))) : Stacks t a :=
  ⟨[], [], [], [], [], [], fun _ => [], fun i => if i = tape0 M then w else []⟩

/-- Stacks holding only the output. -/
def outputStacks (l : List Bool) : Stacks t a :=
  ⟨[], l, [], [], [], [], fun _ => [], fun _ => []⟩

/-- The common padded length of the two factors. -/
def padLen (A B : ℕ) : ℕ := max (max (encodeNat A).length (encodeNat B).length) 1

/-- The most-significant-first word of `A` padded to length `n`. -/
def msbWord (n A : ℕ) : List Bool := (padTo n (encodeNat A)).reverse

lemma length_padTo {n : ℕ} {l : List Bool} (h : l.length ≤ n) : (padTo n l).length = n := by
  simp [padTo]; omega

lemma binaryValue_msbWord (n A : ℕ) : binaryValue (msbWord n A) = A := by
  simp only [msbWord, padTo, List.reverse_append, List.reverse_replicate,
    binaryValue_replicate_append, binaryValue_reverse_encodeNat]

section
variable (body : Unit → Pr t q a)

lemma peekFlag_run (k : BK t) (v : BS t q a) (S : Stacks t a) :
    (peekFlag k : Act t q a).run (mk v S) = mk { v with flag := (S.get k).head?.isSome } S := rfl

lemma drain_of_loop {k : BK t} {b : Act t q a} {v : BS t q a} {S : Stacks t a} {n : ℕ}
    {u : Store (BΓ (t := t) a) (BS t q a)}
    (h : Exec body (.loop (·.flag) (.act b)) (mk { v with flag := (S.get k).head?.isSome } S) n u) :
    Exec body (drain k b) (mk v S) (1 + n) u :=
  Exec.seq (peekFlag_run k v S ▸ Exec.act (body := body) (peekFlag k) (mk v S)) h

theorem prepare_exec (M : Program t q a) (A B : ℕ) (v : BS t q a) :
    ∃ v' m, Keeps v v' ∧
      m ≤ 30 * ((encodeNat A).length + (encodeNat B).length) + 40 ∧
      Exec body (prepare M) (mk v (inputStacks ((encodingProd encodingNatBool encodingNatBool).encode (A, B))))
        m (mk v' (tapeStacks M ((msbWord (padLen A B) A).map bitSymbol ++ [separator] ++
          (msbWord (padLen A B) B).map bitSymbol))) := by
  set eA := encodeNat A
  set eB := encodeNat B
  set n := padLen A B
  set n' := max eA.length eB.length
  set x := msbWord n A
  set y := msbWord n B
  set i₀ := tape0 M
  set P := (encodingProd encodingNatBool encodingNatBool).encode (A, B)
  have hP : P = eA.map Sum.inl ++ eB.map Sum.inr := rfl
  have hPl : P.filterMap Sum.getLeft? = eA := by
    simp [hP, List.filterMap_append, List.filterMap_map, Function.comp_def]
  have hPr : P.filterMap Sum.getRight? = eB := by
    simp [hP, List.filterMap_append, List.filterMap_map, Function.comp_def]
  -- 1. split
  obtain ⟨v₁, k₁, e₁⟩ := split_loop body P { v with flag := P.head?.isSome } (inputStacks P) rfl rfl
  set S₁ : Stacks t a := { (inputStacks P : Stacks t a) with
    inp := []
    b0 := (P.filterMap Sum.getLeft?).reverse ++ (inputStacks P : Stacks t a).b0
    b1 := (P.filterMap Sum.getRight?).reverse ++ (inputStacks P : Stacks t a).b1 }
  have hS₁0 : S₁.b0 = eA.reverse := by simp [S₁, hPl, inputStacks]
  have hS₁1 : S₁.b1 = eB.reverse := by simp [S₁, hPr, inputStacks]
  -- 2. bit 0 → bit 2
  obtain ⟨v₂, k₂, e₂⟩ := moveBit02_loop body S₁.b0 { v₁ with flag := S₁.b0.head?.isSome } S₁ rfl rfl
  set S₂ : Stacks t a := { S₁ with
    b0 := []
    b2 := S₁.b0.reverse ++ S₁.b2 }
  -- 3. bit 1 → bit 3
  obtain ⟨v₃, k₃, e₃⟩ := moveBit13_loop body S₂.b1 { v₂ with flag := S₂.b1.head?.isSome } S₂ rfl rfl
  set S₃ : Stacks t a := { S₂ with
    b1 := []
    b3 := S₂.b1.reverse ++ S₂.b3 }
  have hS₃2 : S₃.b2 = eA := by simp [S₃, S₂, S₁, inputStacks, hPl]
  have hS₃3 : S₃.b3 = eB := by simp [S₃, S₂, S₁, inputStacks, hPr]
  -- 4. lockstep padding
  have hlp : (lockPeek : Act t q a).run (mk v₃ S₃) = mk { v₃ with
      x := S₃.b2.head?
      y := S₃.b3.head?
      flag := S₃.b2.head?.isSome || S₃.b3.head?.isSome } S₃ := by
    simp [lockPeek, Action.run]
  obtain ⟨v₄, k₄, e₄⟩ := lock_loop body n' S₃.b2 S₃.b3 { v₃ with
      x := S₃.b2.head?
      y := S₃.b3.head?
      flag := S₃.b2.head?.isSome || S₃.b3.head?.isSome } S₃ (by rw [hS₃2, hS₃3]) rfl rfl rfl
  set S₄ : Stacks t a := { S₃ with
    b2 := []
    b3 := []
    b0 := (padTo n' S₃.b2).reverse ++ S₃.b0
    b1 := (padTo n' S₃.b3).reverse ++ S₃.b1 }
  -- 5. pad an empty pair to one bit each
  obtain ⟨v₅, k₅, h₅⟩ := padEmpty_run v₄ S₄
  set S₅ : Stacks t a := if S₄.b0 = [] then { S₄ with
    b0 := [false]
    b1 := false :: S₄.b1 } else S₄
  have hS₅ : S₅ = { S₄ with
      b0 := x
      b1 := y } := by
    have h4 : S₄.b0 = (padTo n' eA).reverse ∧ S₄.b1 = (padTo n' eB).reverse := by
      simp [S₄, S₃, S₂, S₁, hS₃2, hS₃3, inputStacks, hPl, hPr]
    by_cases hz : n' = 0
    · have hA : eA = [] := List.length_eq_zero_iff.1 (by omega)
      have hB : eB = [] := List.length_eq_zero_iff.1 (by omega)
      have hn : n = 1 := by show max n' 1 = 1; rw [hz]; rfl
      have hx : x = [false] := by show (padTo n eA).reverse = [false]; rw [hn, hA]; rfl
      have hy : y = [false] := by show (padTo n eB).reverse = [false]; rw [hn, hB]; rfl
      have hb0 : S₄.b0 = [] := by rw [h4.1, hz, hA]; rfl
      have hb1 : S₄.b1 = [] := by rw [h4.2, hz, hB]; rfl
      simp only [S₅, hb0, ite_true, hx, hy, hb1]
    · have hn : n = n' := by show max n' 1 = n'; omega
      have hb0 : S₄.b0 ≠ [] := by
        rw [h4.1]
        intro h
        have := congrArg List.length h
        rw [List.length_reverse, length_padTo (le_max_left _ _ : eA.length ≤ n')] at this
        exact hz this
      have hx : x = S₄.b0 := by rw [h4.1]; show (padTo n eA).reverse = _; rw [hn]
      have hy : y = S₄.b1 := by rw [h4.2]; show (padTo n eB).reverse = _; rw [hn]
      simp only [S₅, hb0, ite_false, hx, hy]
  -- 6. bit 1 → bit 3
  obtain ⟨v₆, k₆, e₆⟩ := moveBit13_loop body S₅.b1 { v₅ with flag := S₅.b1.head?.isSome } S₅ rfl rfl
  set S₆ : Stacks t a := { S₅ with
    b1 := []
    b3 := S₅.b1.reverse ++ S₅.b3 }
  -- 7. bit 3 → tape 0
  obtain ⟨v₇, k₇, e₇⟩ := toTape3_loop body i₀ S₆.b3 { v₆ with flag := S₆.b3.head?.isSome } S₆ rfl (by dsimp only)
  set S₇ : Stacks t a := { S₆ with
    b3 := []
    R := Function.update S₆.R i₀ ((S₆.b3.map bitSymbol).reverse ++ S₆.R i₀) }
  -- 8. separator
  have h₈ : (pushSep i₀ : Act t q a).run (mk v₇ S₇) =
      mk v₇ { S₇ with R := Function.update S₇.R i₀ (separator :: S₇.R i₀) } := by
    simp [pushSep, Action.run, update_rt]
  set S₈ : Stacks t a := { S₇ with R := Function.update S₇.R i₀ (separator :: S₇.R i₀) }
  -- 9. bit 0 → bit 2
  obtain ⟨v₉, k₉, e₉⟩ := moveBit02_loop body S₈.b0 { v₇ with flag := S₈.b0.head?.isSome } S₈ rfl rfl
  set S₉ : Stacks t a := { S₈ with
    b0 := []
    b2 := S₈.b0.reverse ++ S₈.b2 }
  -- 10. bit 2 → tape 0
  obtain ⟨v₁₀, k₁₀, e₁₀⟩ := toTape2_loop body i₀ S₉.b2 { v₉ with flag := S₉.b2.head?.isSome } S₉ rfl (by dsimp only)
  set S₁₀ : Stacks t a := { S₉ with
    b2 := []
    R := Function.update S₉.R i₀ ((S₉.b2.map bitSymbol).reverse ++ S₉.R i₀) }
  -- contents
  have hS₄e : S₄.inp = [] ∧ S₄.out = [] ∧ S₄.b2 = [] ∧ S₄.b3 = [] ∧ S₄.L = (fun _ => []) ∧
      S₄.R = (fun _ => []) := by
    simp [S₄, S₃, S₂, S₁, inputStacks]
  have hfin : S₁₀ = tapeStacks M (x.map bitSymbol ++ [separator] ++ y.map bitSymbol) := by
    have h5 := hS₅
    refine Stacks.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [S₁₀, S₉, S₈, S₇, S₆, h5, hS₄e.1, tapeStacks]
    · simp [S₁₀, S₉, S₈, S₇, S₆, h5, hS₄e.2.1, tapeStacks]
    · simp [S₁₀, S₉, S₈, S₇, S₆, tapeStacks]
    · simp [S₁₀, S₉, S₈, S₇, S₆, tapeStacks]
    · simp [S₁₀, tapeStacks]
    · simp [S₁₀, S₉, S₈, S₇, tapeStacks]
    · simp [S₁₀, S₉, S₈, S₇, S₆, h5, hS₄e.2.2.2.2.1, tapeStacks]
    · funext i
      by_cases hi : i = i₀
      · subst hi
        simp [S₁₀, S₉, S₈, S₇, S₆, h5, hS₄e.2.2.1, hS₄e.2.2.2.1, hS₄e.2.2.2.2.2, tapeStacks, i₀,
          List.map_reverse]
      · simp [S₁₀, S₉, S₈, S₇, S₆, h5, hS₄e.2.2.2.2.2, tapeStacks, hi, i₀, Function.update_of_ne hi]
  -- lengths
  have hlP : P.length = eA.length + eB.length := by simp [hP]
  have hn1 : n ≤ eA.length + eB.length + 1 := by show max n' 1 ≤ _; omega
  have hnA : eA.length ≤ n := by show _ ≤ max n' 1; omega
  have hnB : eB.length ≤ n := by show _ ≤ max n' 1; omega
  have hlx : x.length = n := by
    show (padTo n eA).reverse.length = n; rw [List.length_reverse, length_padTo hnA]
  have hly : y.length = n := by
    show (padTo n eB).reverse.length = n; rw [List.length_reverse, length_padTo hnB]
  have hl1 : S₁.b0.length = eA.length := by rw [hS₁0, List.length_reverse]
  have hl2 : S₂.b1.length = eB.length := by
    show S₁.b1.length = _; rw [hS₁1, List.length_reverse]
  have hl5 : S₅.b1.length = n := by rw [hS₅]; exact hly
  have hl6 : S₆.b3.length = n := by
    show (S₅.b1.reverse ++ S₅.b3).length = n
    rw [hS₅]; simp [hly, hS₄e.2.2.2.1]
  have hl8 : S₈.b0.length = n := by
    show S₅.b0.length = n; rw [hS₅]; exact hlx
  have hl9 : S₉.b2.length = n := by
    show (S₈.b0.reverse ++ S₈.b2).length = n
    have : S₈.b2 = [] := by show S₅.b2 = []; rw [hS₅]
    rw [this]; simp [hl8]
  have hn' : n' ≤ eA.length + eB.length := by simp only [n']; omega
  refine ⟨v₁₀, _, ?_, ?_, Exec.cast
    (Exec.seq (drain_of_loop body e₁)
    (Exec.seq (drain_of_loop body e₂)
    (Exec.seq (drain_of_loop body e₃)
    (Exec.seq (Exec.seq (hlp ▸ Exec.act (body := body) lockPeek (mk v₃ S₃)) e₄)
    (Exec.seq (h₅ ▸ Exec.act (body := body) padEmpty (mk v₄ S₄))
    (Exec.seq (drain_of_loop body e₆)
    (Exec.seq (drain_of_loop body e₇)
    (Exec.seq (h₈ ▸ Exec.act (body := body) (pushSep i₀) (mk v₇ S₇))
    (Exec.seq (drain_of_loop body e₉)
    (Exec.seq (drain_of_loop body e₁₀)
      (Exec.act (body := body) .done _)))))))))))
    rfl (by rw [← hfin]; rfl)⟩
  -- Compose the two preserved fields directly, avoiding inference of whole intermediate states.
  · exact ⟨k₁₀.1.trans (k₉.1.trans (k₇.1.trans (k₆.1.trans (k₅.1.trans
        (k₄.1.trans (k₃.1.trans (k₂.1.trans k₁.1))))))),
      k₁₀.2.trans (k₉.2.trans (k₇.2.trans (k₆.2.trans (k₅.2.trans
        (k₄.2.trans (k₃.2.trans (k₂.2.trans k₁.2)))))))⟩
  · rw [hlP, hl1, hl2, hl5, hl6, hl8, hl9]
    omega

theorem cleanup_exec : ∀ (l : List (Fin t)) (v : BS t q a) (S : Stacks t a),
    ∃ v' m, Keeps v v' ∧
      m ≤ (l.map fun i => 2 * (S.L i).length + 2 * (S.R i).length + 4).sum + 1 ∧
      Exec body (Prog.seqList (l.flatMap fun i =>
          [drain (.lt i) (dropStep (.lt i)), drain (.rt i) (dropStep (.rt i))])) (mk v S) m
        (mk v' { S with
          L := fun i => if i ∈ l then [] else S.L i
          R := fun i => if i ∈ l then [] else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro v S
      refine ⟨v, 1, Keeps.refl v, by simp, ?_⟩
      have : ({ S with
          L := fun i => if i ∈ ([] : List (Fin t)) then [] else S.L i
          R := fun i => if i ∈ ([] : List (Fin t)) then [] else S.R i } : Stacks t a) = S := by
        cases S; simp
      rw [this]
      exact Exec.act (body := body) .done (mk v S)
  | cons i rest ih =>
      intro v S
      obtain ⟨v₁, k₁, e₁⟩ := dropL_loop body i (S.L i) { v with flag := (S.L i).head?.isSome } S rfl rfl
      set S₁ : Stacks t a := { S with L := Function.update S.L i [] }
      obtain ⟨v₂, k₂, e₂⟩ := dropR_loop body i (S₁.R i) { v₁ with flag := (S₁.R i).head?.isSome } S₁
        rfl rfl
      set S₂ : Stacks t a := { S₁ with R := Function.update S₁.R i [] }
      obtain ⟨v₃, m, k₃, hm, e₃⟩ := ih v₂ S₂
      refine ⟨v₃, _, (Keeps.trans ⟨rfl, rfl⟩ k₁).trans ((Keeps.trans ⟨rfl, rfl⟩ k₂).trans k₃), ?_,
        Exec.cast (Exec.seq (drain_of_loop body e₁) (Exec.seq (drain_of_loop body e₂) e₃)) rfl ?_⟩
      · have hle : (rest.map fun j => 2 * (S₂.L j).length + 2 * (S₂.R j).length + 4).sum ≤
            (rest.map fun j => 2 * (S.L j).length + 2 * (S.R j).length + 4).sum := by
          apply List.sum_le_sum
          intro j _
          by_cases hj : j = i
          · subst hj; simp [S₂, S₁]
          · simp [S₂, S₁, Function.update_of_ne hj]
        simp only [List.map_cons, List.sum_cons]
        have : (S₁.R i).length = (S.R i).length := rfl
        omega
      · congr 1
        refine Stacks.ext rfl rfl rfl rfl rfl rfl ?_ ?_
        · funext j
          by_cases hj : j = i
          · subst hj; simp [S₂, S₁]
          · simp [S₂, S₁, hj, Function.update_of_ne hj]
        · funext j
          by_cases hj : j = i
          · subst hj; simp [S₂, S₁]
          · simp [S₂, S₁, hj, Function.update_of_ne hj]

theorem finish_exec (M : Program t q a) (v : BS t q a) (S : Stacks t a) (cf : Config t q a)
    (out : List Bool) (hv : v.lead = true) (hrep : Rep cf S.L S.R)
    (hS : S.inp = [] ∧ S.out = [] ∧ S.b0 = [] ∧ S.b1 = [] ∧ S.b2 = [] ∧ S.b3 = [])
    (hne : out ≠ []) (hT : cf.tape (tape0 M) = wordTape (out.map bitSymbol)) (Z : ℕ)
    (hZ : ∀ i, (S.L i).length + (S.R i).length ≤ Z) :
    ∃ m, m ≤ 6 * t * Z + 4 * t + 10 ∧
      Exec body (finish M) (mk v S) m (mk (init M) (outputStacks (encodeNat (binaryValue out)))) := by
  set i₀ := tape0 M
  -- move the left part of tape 0 onto its right stack
  obtain ⟨v₁, k₁, e₁⟩ := leftToRight_loop body i₀ (S.L i₀) { v with flag := (S.L i₀).head?.isSome } S
    rfl rfl
  set S₁ : Stacks t a := { S with
    L := Function.update S.L i₀ []
    R := Function.update S.R i₀ ((S.L i₀).reverse ++ S.R i₀) }
  -- emit the bits
  set W := (S.L i₀).reverse ++ S.R i₀
  obtain ⟨v₂, k₂, e₂⟩ := extract_loop body i₀ W { v₁ with flag := W.head?.isSome } S₁
    (by simp [S₁, W]) rfl
  have hlead : ({ v₁ with flag := W.head?.isSome } : BS t q a).lead = true := by
    rw [← hv]; exact k₁.1
  set S₂ : Stacks t a := { S₁ with
    R := Function.update S₁.R i₀ []
    out := emitted ({ v₁ with flag := W.head?.isSome } : BS t q a).lead W ++ S₁.out }
  have hW : W.filterMap decodeBit = out := by
    apply filterMap_window (S.L i₀) (S.R i₀) (cf.head i₀) out hne
    intro j
    rw [← hT]
    exact hrep i₀ j
  have hemit : emitted ({ v₁ with flag := W.head?.isSome } : BS t q a).lead W ++ S₁.out =
      encodeNat (binaryValue out) := by
    rw [hlead, encodeNat_binaryValue]
    simp [emitted, hW, S₁, hS.2.1]
  -- clear every tape
  obtain ⟨v₃, m₃, k₃, hm₃, e₃⟩ := cleanup_exec body (List.finRange t) v₂ S₂
  have hfin : ({ S₂ with
      L := fun i => if i ∈ List.finRange t then [] else S₂.L i
      R := fun i => if i ∈ List.finRange t then [] else S₂.R i } : Stacks t a) =
      outputStacks (encodeNat (binaryValue out)) := by
    refine Stacks.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [S₂, S₁, hS.1, outputStacks]
    · simp only [S₂]; rw [hemit]; rfl
    · simp [S₂, S₁, hS.2.2.1, outputStacks]
    · simp [S₂, S₁, hS.2.2.2.1, outputStacks]
    · simp [S₂, S₁, hS.2.2.2.2.1, outputStacks]
    · simp [S₂, S₁, hS.2.2.2.2.2, outputStacks]
    · funext i; simp [outputStacks]
    · funext i; simp [outputStacks]
  rw [hfin] at e₃
  have hreset : (Action.load (fun _ => init M) .done : Act t q a).run
      (mk v₃ (outputStacks (encodeNat (binaryValue out)))) =
      mk (init M) (outputStacks (encodeNat (binaryValue out))) := rfl
  refine ⟨_, ?_, Exec.seq (drain_of_loop body e₁) (Exec.seq (drain_of_loop body e₂)
    (Exec.seq e₃ (Exec.seq (hreset ▸ Exec.act (body := body) _ _)
      (Exec.act (body := body) .done _))))⟩
  -- cost
  have hsum : ((List.finRange t).map fun i =>
      2 * (S₂.L i).length + 2 * (S₂.R i).length + 4).sum ≤ t * (2 * Z + 4) := by
    have := List.sum_le_length_nsmul ((List.finRange t).map fun i =>
      2 * (S₂.L i).length + 2 * (S₂.R i).length + 4) (2 * Z + 4) (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨i, -, rfl⟩ := hx
        by_cases hi : i = i₀
        · subst hi; simp [S₂, S₁]
        · have := hZ i
          simp [S₂, S₁, Function.update_of_ne hi]
          omega)
    simpa using this
  have h0 := hZ i₀
  have hWZ : W.length ≤ Z := by simp only [W, List.length_append, List.length_reverse]; exact h0
  have h1 : t * (2 * Z + 4) = 2 * (t * Z) + 4 * t := by ring
  have h2 : 6 * t * Z = 6 * (t * Z) := by ring
  have ht1 : 1 ≤ t := M.tapes_pos
  have h3 : Z ≤ t * Z := Nat.le_mul_of_pos_left Z ht1
  omega

end

end IntegerMultBounds.MathlibTM2
