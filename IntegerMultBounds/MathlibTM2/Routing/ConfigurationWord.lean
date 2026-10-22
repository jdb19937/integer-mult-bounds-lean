module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-!
# Read one framed configuration word with an explicit rewind archive

The archive is a right stack. Keeping consumed configuration off left stacks is
necessary because the actual interchange program requires empty left stacks.
The fixed scanner duplicates symbols to the destination scratch and archive;
rewinding the archive later restores the complete configuration input.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def configurationScanStep (src tmp saved : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .pop (.rt src) (fun v x => { v with sym := x })
    (.push (.rt tmp) (fun v => v.sym.getD blank)
      (.push (.rt saved) (fun v => v.sym.getD blank) (WordCmd.peekRp src p)))

def configurationScanned (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (word rest : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R src rest) tmp (word.reverse ++ R tmp))
    saved (word.reverse ++ R saved)

/-- Scan a single word, stopping at its framing symbol. No tape count or code
size depends on the word length. -/
theorem configurationScan_loop (body : P → Pr P T Q A U) (src tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (p : Fin (A + 4) → Bool) (rest : List (Fin (A + 4)))
    (hrest : (rest.head?.map p).getD false = false) :
    ∀ (word : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ word, p x = true) → S.R src = word ++ rest →
      v.flag = ((word ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (configurationScanStep src tmp saved p)))
          (mk v S) (2 * word.length + 1)
          (mk v' { S with R := configurationScanned S.R src tmp saved word rest }) := by
  intro word
  induction word with
  | nil =>
    intro v S hword hsrc hflag
    have he : configurationScanned S.R src tmp saved [] rest = S.R := by
      have hs : S.R src = rest := by simpa using hsrc
      rw [← hs]
      simp [configurationScanned]
    refine ⟨v, rfl, ?_⟩
    rw [he]
    exact Exec.loop_false (by simpa only [List.nil_append, hrest, mk_var] using hflag)

  | cons x word ih =>
    intro v S hword hsrc hflag
    have hx := hword x (by simp)
    let R₁ := Function.update (Function.update (Function.update S.R src (word ++ rest))
      tmp (x :: S.R tmp)) saved (x :: S.R saved)
    let v₁ := { v with sym := some x, flag := ((word ++ rest).head?.map p).getD false }
    obtain ⟨v₂, hu, he⟩ := ih v₁ { S with R := R₁ }
      (fun y hy => hword y (by simp [hy]))
      (by simp [R₁, Function.update_of_ne hss, Function.update_of_ne hst]) rfl
    have hrun : (configurationScanStep src tmp saved p : Act T Q A U).run (mk v S) =
        mk v₁ { S with R := R₁ } := by
      simp [configurationScanStep, WordCmd.peekRp, Action.run, hsrc, update_rt,
        Function.update_of_ne hss, Function.update_of_ne hst, R₁, v₁,
        Function.update_of_ne hts.symm,
        Function.update_of_ne hss.symm, Function.update_of_ne hst.symm]
    have hfinal : configurationScanned R₁ src tmp saved word rest =
        configurationScanned S.R src tmp saved (x :: word) rest := by
      funext j
      by_cases hj : j = saved
      · subst j
        simp [configurationScanned, R₁, List.reverse_cons, List.append_assoc,
          ]
      · by_cases hj' : j = tmp
        · subst j
          simp [configurationScanned, R₁, hj, List.reverse_cons, List.append_assoc]
        · by_cases hj'' : j = src
          · subst j
            simp [configurationScanned, R₁, hj, hj']
          · simp [configurationScanned, R₁, hj, hj', hj'']
    refine ⟨v₂, hu, ?_⟩
    have hex := Exec.loop_true (body := body) (f := (·.flag))
      (by simpa [hx] using hflag) (hrun ▸ Exec.act (body := body) (configurationScanStep src tmp saved p) (mk v S)) he
    refine Exec.cast hex (by simp; ring) ?_
    congr 2

def configurationScan (src tmp saved : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (WordCmd.peekRp src p)) (.loop (·.flag) (.act (configurationScanStep src tmp saved p)))

theorem configurationScan_exec (body : P → Pr P T Q A U) (src tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (p : Fin (A + 4) → Bool) (word rest : List (Fin (A + 4)))
    (hword : ∀ x ∈ word, p x = true) (hrest : (rest.head?.map p).getD false = false)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = word ++ rest) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationScan src tmp saved p) (mk v S) (2 * word.length + 2)
        (mk v' { S with R := configurationScanned S.R src tmp saved word rest }) := by
  let v₀ := { v with flag := ((word ++ rest).head?.map p).getD false }
  obtain ⟨v', hu, he⟩ := configurationScan_loop body src tmp saved hst hss hts p rest hrest
    word v₀ S hword hsrc rfl
  have hp : (WordCmd.peekRp src p : Act T Q A U).run (mk v S) = mk v₀ S := by
    simp [WordCmd.peekRp, Action.run, hsrc, v₀]
  refine ⟨v', hu, ?_⟩
  exact Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) (WordCmd.peekRp src p) (mk v S)) he)
    (by omega) rfl

/-- Rewind the right-stack archive, restoring all consumed configuration symbols
in their original order. All other registers and all left stacks are unchanged. -/
theorem configurationRestore_exec (body : P → Pr P T Q A U) (src saved : Fin T)
    (hss : saved ≠ src) (consumed rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsaved : S.R saved = consumed.reverse) (hsrc : S.R src = rest) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveR saved src id) (mk v S) (2 * consumed.length + 2)
        (mk v' { S with R := Function.update (Function.update S.R saved []) src (consumed ++ rest) }) := by
  obtain ⟨v', hu, he⟩ := moveR_exec body saved src hss id v S
  refine ⟨v', hu, ?_⟩
  simpa only [hsaved, List.length_reverse, movedR, List.map_id, List.reverse_reverse, hsrc] using he

end IntegerMultBounds.MathlibTM2.Routing
