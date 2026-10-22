module

public import IntegerMultBounds.MathlibTM2.Routing.ReadRow

/-!
# Fixed-program ordered source gathering

Each descriptor row is a mask of the source width. Rows are interpreted in their
given order, so singleton masks describe arbitrary ordered (and repeated) source
positions. The complete descriptor and source are restored and all scratch is
cleared. The quadratic metadata cost is explicit; its amortization against long
records is a separate caller obligation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Gather all descriptor rows in order, then restore descriptor and output order. -/
def readRows (src desc st saved rev out cs : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR desc))
    (.seq (.loop (·.flag)
      (.seq (readRow src desc st saved rev cs) (.act (peekR desc))))
      (.seq (moveR saved desc id) (moveR rev out id)))

private def rowsFile (R : Fin T → List (Fin (A + 4))) (desc saved rev : Fin T)
    (ss : List Bool) (rows : List (List Bool)) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R desc []) saved
    ((rows.flatten.map bitSymbol).reverse ++ R saved)) rev
      ((((rows.flatMap (gatherL ss)).map bitSymbol).reverse) ++ R rev)

private theorem readRows_loop {src desc st saved rev cs : Fin T}
    (h : [src, desc, st, saved, rev].Nodup) (ss : List Bool) (hss : 0 < ss.length) :
    ∀ (rows : List (List Bool)) (v : HS T Q A U) (S : Stacks T A),
      (∀ ms ∈ rows, ms.length = ss.length) → S.R src = ss.map bitSymbol →
      S.R desc = rows.flatten.map bitSymbol → S.R st = [] →
      v.flag = rows.flatten.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag)
          (.seq (readRow src desc st saved rev cs) (.act (peekR desc)))) (mk v S)
          (rows.length * (4 * ss.length + 6) + 1)
          (mk v' { S with R := rowsFile S.R desc saved rev ss rows }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  intro rows
  induction rows with
  | nil =>
    intro v S _ hs hd hst hf
    have he : ({ S with R := rowsFile S.R desc saved rev ss [] } : Stacks T A) = S := by
      congr 1
      funext k
      simp [rowsFile, Function.update_apply]
      split_ifs <;> simp_all
    rw [he]
    refine ⟨v, rfl, ?_⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    apply Exec.loop_false
    simpa using hf
  | cons ms rows ih =>
    intro v S hlen hs hd hst hf
    have hm : ms.length = ss.length := hlen ms (by simp)
    have hmpos : 0 < ms.length := by omega
    have hf' : v.flag = true := by
      rw [hf]
      cases ms with
      | nil => simp at hmpos
      | cons m ms => simp
    obtain ⟨v₁, hu₁, he₁⟩ := readRow_exec body (cs := cs) h ss ms (rows.flatten.map bitSymbol)
      hm.symm v S hs (by simpa using hd) hst
    let R₁ := Function.update (Function.update (Function.update S.R desc (rows.flatten.map bitSymbol))
      saved ((ms.map bitSymbol).reverse ++ S.R saved)) rev
        (((gatherL ss ms).map bitSymbol).reverse ++ S.R rev)
    have hdesc : R₁ desc = rows.flatten.map bitSymbol := by
      simp [R₁, b2, b3]
    have hp : (peekR desc : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
        mk { v₁ with flag := rows.flatten.head?.isSome } { S with R := R₁ } := by
      rw [peekR_run]
      change mk { v₁ with flag := (R₁ desc).head?.isSome } _ = _
      rw [hdesc]
      generalize rows.flatten = flat
      cases flat <;> rfl
    obtain ⟨v₂, hu₂, he₂⟩ := ih { v₁ with flag := rows.flatten.head?.isSome }
      { S with R := R₁ } (fun ms hm => hlen ms (by simp [hm]))
      (by simp [R₁, a1, a3, a4, hs]) hdesc (by simp [R₁, Ne.symm b1, c1, c2, hst]) rfl
    refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.loop_true hf'
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR desc) (mk v₁ { S with R := R₁ }))) he₂)
        (by simp; ring) ?_⟩
    congr 2
    funext k
    simp [rowsFile, R₁, Function.update_apply, List.reverse_append, List.append_assoc]
    split_ifs <;> simp_all

/-- Exact runtime of the scanner, including restoring the descriptor and reversing output. -/
def readRowsCost (ss : List Bool) (rows : List (List Bool)) : ℕ :=
  rows.length * (4 * ss.length + 6) + 2 * rows.flatten.length +
    2 * (rows.flatMap (gatherL ss)).length + 6

/-- The source and full ordered descriptor are restored. Only `out` changes; the
three scratch registers start and end empty. The program contains no source indices. -/
theorem readRows_exec {src desc st saved rev out cs : Fin T}
    (h : [src, desc, st, saved, rev, out].Nodup) (ss : List Bool) (hss : 0 < ss.length)
    (rows : List (List Bool)) (hlen : ∀ ms ∈ rows, ms.length = ss.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = ss.map bitSymbol) (hd : S.R desc = rows.flatten.map bitSymbol)
    (hst : S.R st = []) (hsaved : S.R saved = []) (hrev : S.R rev = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readRows src desc st saved rev out cs) (mk v S) (readRowsCost ss rows)
        (mk v' { S with
          R := Function.update S.R out ((rows.flatMap (gatherL ss)).map bitSymbol ++ S.R out) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hn
  have h5 : [src, desc, st, saved, rev].Nodup := by simp_all
  obtain ⟨v₁, hu₁, he₁⟩ := readRows_loop body h5 ss hss rows
    { v with flag := (S.R desc).head?.isSome } S hlen hs hd hst
    (by rw [hd]; cases rows.flatten <;> rfl)
  let R₁ := rowsFile S.R desc saved rev ss rows
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved desc (Ne.symm b2) id v₁ { S with R := R₁ }
  let R₂ := movedR R₁ saved desc id (R₁ saved)
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body rev out e1 id v₂ { S with R := R₂ }
  have hsave : R₁ saved = (rows.flatten.map bitSymbol).reverse := by
    simp [R₁, rowsFile, d1, hsaved]
  have hout : R₂ rev = ((rows.flatMap (gatherL ss)).map bitSymbol).reverse := by
    simp [R₂, movedR, R₁, rowsFile, Ne.symm b3, Ne.symm d1, hrev]
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.cast
    (Exec.seq (peekR_run desc v S ▸ Exec.act (body := body) (peekR desc) (mk v S))
      (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · change 1 + (rows.length * (4 * ss.length + 6) + 1 +
      ((2 * (R₁ saved).length + 2) + (2 * (R₂ rev).length + 2))) = _
    rw [hsave, hout]
    simp only [List.length_reverse, List.length_map, readRowsCost]
    omega
  · congr 2
    funext k
    simp [R₂, R₁, rowsFile, movedR, Function.update_apply]
    split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Routing
