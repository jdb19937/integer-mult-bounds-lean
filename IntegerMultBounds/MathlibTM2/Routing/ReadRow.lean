module

public import IntegerMultBounds.MathlibTM2.Host.GatherSpread

/-!
# One row of the ordered source-descriptor scanner

A row of mask bits is consumed from a descriptor table while the source is
scanned. Both consumed lists are saved in reverse; the source is then restored.
The table may contain further rows. Output is accumulated in reverse for a final
linear reversal. The program is independent of row width and source positions.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Scan one source symbol and one descriptor bit, saving both and selecting
that symbol precisely when the descriptor bit is set. -/
def readRowStep (src desc st saved rev cs : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.pop (.rt desc) (fun v o => { v with scan := Function.update v.scan cs (o.getD blank) })
      (.push (.rt st) (fun v => v.sym.getD blank)
        (.push (.rt saved) (fun v => v.scan cs)
          (.branch (fun v => symBit (v.scan cs))
            (.push (.rt rev) (fun v => v.sym.getD blank) (peekR src)) (peekR src)))))

/-- The complete scanner for one descriptor row, restoring the source. -/
def readRow (src desc st saved rev cs : Fin T) : Pr P T Q A U :=
  .seq (whileR src (readRowStep src desc st saved rev cs)) (moveR st src id)

private def rowFile (R : Fin T → List (Fin (A + 4))) (src desc st saved rev : Fin T)
    (rest : List (Fin (A + 4))) (ss ms : List Bool) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    R src []) desc rest) st ((ss.map bitSymbol).reverse ++ R st)) saved
      ((ms.map bitSymbol).reverse ++ R saved)) rev
        (((gatherL ss ms).map bitSymbol).reverse ++ R rev)

private theorem readRow_loop {src desc st saved rev cs : Fin T}
    (h : [src, desc, st, saved, rev].Nodup) :
    ∀ (ss ms : List Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      ss.length = ms.length → S.R src = ss.map bitSymbol →
      S.R desc = ms.map bitSymbol ++ rest → v.flag = ss.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (readRowStep src desc st saved rev cs))) (mk v S)
          (2 * ss.length + 1)
          (mk v' { S with R := rowFile S.R src desc st saved rev rest ss ms }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  intro ss
  induction ss with
  | nil =>
    intro ms rest v S hl hs hd hf
    have hm : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst ms
    have he : ({ S with R := rowFile S.R src desc st saved rev rest [] [] } : Stacks T A) = S := by
      congr 1
      funext k
      simp [rowFile, gatherL, Function.update_apply]
      split_ifs <;> simp_all
    rw [he]
    exact ⟨v, rfl, Exec.loop_false (by simpa using hf)⟩
  | cons s ss ih =>
    intro ms rest v S hl hs hd hf
    cases ms with
    | nil => simp at hl
    | cons m ms =>
      set R₁ := Function.update (Function.update (Function.update (Function.update S.R
        src (ss.map bitSymbol)) desc (ms.map bitSymbol ++ rest)) st
          (bitSymbol s :: S.R st)) saved (bitSymbol m :: S.R saved) with hR₁
      set R₂ := if m then Function.update R₁ rev (bitSymbol s :: S.R rev) else R₁ with hR₂
      have hrun : (readRowStep src desc st saved rev cs : Act T Q A U).run (mk v S) =
          mk { v with
            sym := some (bitSymbol s)
            scan := Function.update v.scan cs (bitSymbol m)
            flag := ss.head?.isSome } { S with R := R₂ } := by
        cases m <;>
          simp [readRowStep, Action.run, update_rt, peekR, hs, hd, R₂, R₁,
            a1, a2, a3, a4, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
            Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm c1, Ne.symm c2, Ne.symm d1]
      obtain ⟨v', hu, he⟩ := ih ms rest
        { v with
          sym := some (bitSymbol s)
          scan := Function.update v.scan cs (bitSymbol m)
          flag := ss.head?.isSome } { S with R := R₂ } (by simpa using hl)
        (by cases m <;> simp [R₂, R₁, a1, a2, a3, a4])
        (by cases m <;> simp [R₂, R₁, b1, b2, b3]) rfl
      refine ⟨v', hu, Exec.cast (Exec.loop_true (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (readRowStep src desc st saved rev cs) (mk v S)) he)
          (by simp; ring) ?_⟩
      congr 2
      funext k
      cases m <;>
        simp [rowFile, R₂, R₁, gatherL, Function.update_apply]
        <;> split_ifs <;> simp_all

/-- One row costs exactly four steps per source bit plus four, preserves the
source, consumes one descriptor row and leaves the source temporary empty. -/
theorem readRow_exec {src desc st saved rev cs : Fin T}
    (h : [src, desc, st, saved, rev].Nodup) (ss ms : List Bool)
    (rest : List (Fin (A + 4))) (hl : ss.length = ms.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = ss.map bitSymbol) (hd : S.R desc = ms.map bitSymbol ++ rest)
    (hst : S.R st = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readRow src desc st saved rev cs) (mk v S) (4 * ss.length + 4)
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R desc rest)
            saved ((ms.map bitSymbol).reverse ++ S.R saved)) rev
              (((gatherL ss ms).map bitSymbol).reverse ++ S.R rev) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  obtain ⟨v₁, hu₁, he₁⟩ := readRow_loop body h ss ms rest
    { v with flag := (S.R src).head?.isSome } S hl hs hd
    (by rw [hs]; cases ss <;> rfl)
  let R₁ := rowFile S.R src desc st saved rev rest ss ms
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body st src (Ne.symm a2) id v₁ { S with R := R₁ }
  have ht : R₁ st = (ss.map bitSymbol).reverse := by
    simp [R₁, rowFile, hst, c1, c2]
  refine ⟨v₂, hu₂.trans hu₁, Exec.cast
    (Exec.seq (Exec.seq (peekR_run src v S ▸ Exec.act (body := body) (peekR src) (mk v S)) he₁)
      he₂) (by
        change 1 + (2 * ss.length + 1) + (2 * (R₁ st).length + 2) = _
        rw [ht]
        simp only [List.length_reverse, List.length_map]
        omega) ?_⟩
  congr 2
  funext k
  simp [R₁, rowFile, movedR, Function.update_apply]
  split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Routing
