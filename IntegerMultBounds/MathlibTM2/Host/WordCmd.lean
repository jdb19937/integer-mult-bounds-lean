module

public import IntegerMultBounds.Schoenhage.Ops
public import IntegerMultBounds.MathlibTM2.Host.Stream

/-!
# Word programs on host stacks

The vendored Schönhage–Strassen multiplier is written as a word program (`Schoenhage.Cmd`) over a
bank of word tapes, with big-step semantics `Schoenhage.Exec`. This file runs word programs
directly on host stacks, without a multitape machine in between.

**Word tapes on registers.** A word tape `⟨left, right⟩` on host register `r` has the cells from
the head on (`cells right`) on the right stack and the cells left of the head on the left stack,
nearest on top (`lcells left`: each word as its separator and then its bits from the last).
`place S ι σ` puts the bank `σ` on the injective family of registers `ι`; every other stack keeps
its contents.

**Primitives.** `TImpl C n M` is a host implementation of the primitive `M` with constant `C`: a
host program on any injective family of registers, in any host with at least `n` control states,
that takes the placed tapes of `M` to those of its effect within `C (cost + 1)` steps, with every
other stack and the `user` component unchanged. A primitive with a finite control of its own keeps
it in the host state `st`, hence `n`. `AllTM C n c`: every primitive of `c` has one.

**Compilation** (`tcompile`): primitives by their implementations, sequencing by sequencing, and
the loop and branch tests by a peek at the tested register (`peekW`). `tcompile_exec`: for
`2 ≤ C` and `n ≤ Q`, an execution of `c` within `k` steps gives a host execution of
`tcompile C n ι c` between the placed banks within `C (k + 1)` steps.

**Implemented here:** rewind, back, clear and emit (`rewindImpl`, `backImpl`, `clearImpl`,
`emitImpl`, any `C ≥ 2` and `n`). The streaming primitive is in `Host/WordStream`, reverse and
chunk in `Host/WordCopy`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host.WordCmd

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Schoenhage (WTape Prim Cmd cells clen upd upd_slot upd_other StartsOne)

/-! ### Word tapes on stacks -/

section Cells

variable {A : ℕ}

/-- The cells left of a word tape's head, nearest first. -/
def lcells : List (List Bool) → List (Fin (A + 4))
  | [] => []
  | u :: L => separator :: (u.reverse.map bitSymbol ++ lcells L)

theorem cells_cons' (w : List Bool) (R : List (List Bool)) :
    cells (a := A) (w :: R) = w.map bitSymbol ++ separator :: cells R := by
  simp [cells, Schoenhage.syms_cons, Schoenhage.sym, Function.comp_def]

theorem cells_append' (ws vs : List (List Bool)) :
    cells (a := A) (ws ++ vs) = cells ws ++ cells vs := by
  simp [cells, Schoenhage.syms_append]

theorem lcells_append (L L' : List (List Bool)) :
    lcells (A := A) (L ++ L') = lcells L ++ lcells L' := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [lcells, ih]

theorem lcells_reverse (ws : List (List Bool)) : lcells (A := A) ws.reverse = (cells ws).reverse := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.reverse_cons, lcells_append, ih, cells_cons']
    simp [lcells, List.map_reverse]

theorem reverse_lcells (L : List (List Bool)) : (lcells (A := A) L).reverse = cells L.reverse := by
  rw [← List.reverse_reverse (cells L.reverse), ← lcells_reverse, List.reverse_reverse]

theorem length_lcells (L : List (List Bool)) : (lcells (A := A) L).length = clen L := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [lcells, ih]; ring

theorem cells_head_isSome (R : List (List Bool)) :
    (cells (a := A) R).head?.isSome = decide (R ≠ []) := by
  cases R with
  | nil => rfl
  | cons w R => rw [cells_cons']; cases w <;> simp

theorem cells_head_one (R : List (List Bool)) :
    (cells (a := A) R).head? = some (bitSymbol true) ↔ StartsOne ⟨[], R⟩ := by
  unfold StartsOne
  rcases R with _ | ⟨_ | ⟨b, w⟩, R⟩
  · simp [cells]
  · rw [cells_cons']; simp [separator, bitSymbol]
  · rw [cells_cons']; cases b <;> simp [bitSymbol]

end Cells

section Place

variable {T A t : ℕ}

/-- The stacks `S` with the word tapes `σ` on the registers `ι`. -/
noncomputable def place (S : Stacks T A) (ι : Fin t → Fin T) (σ : Fin t → WTape) : Stacks T A :=
  { S with
    L := fun r => if h : ∃ x, ι x = r then lcells (σ h.choose).left else S.L r
    R := fun r => if h : ∃ x, ι x = r then cells (σ h.choose).right else S.R r }

variable {ι : Fin t → Fin T}

theorem place_L_at (hι : Function.Injective ι) (S : Stacks T A) (σ : Fin t → WTape) (x : Fin t) :
    (place S ι σ).L (ι x) = lcells (σ x).left := by
  have h : ∃ y, ι y = ι x := ⟨x, rfl⟩
  simp only [place, h, ↓reduceDIte]
  rw [hι h.choose_spec]

theorem place_R_at (hι : Function.Injective ι) (S : Stacks T A) (σ : Fin t → WTape) (x : Fin t) :
    (place S ι σ).R (ι x) = cells (σ x).right := by
  have h : ∃ y, ι y = ι x := ⟨x, rfl⟩
  simp only [place, h, ↓reduceDIte]
  rw [hι h.choose_spec]

theorem place_L_off (S : Stacks T A) (σ : Fin t → WTape) {r : Fin T} (hr : ∀ x, ι x ≠ r) :
    (place S ι σ).L r = S.L r := by
  have h : ¬ ∃ x, ι x = r := fun ⟨x, hx⟩ => hr x hx
  simp [place, h]

theorem place_R_off (S : Stacks T A) (σ : Fin t → WTape) {r : Fin T} (hr : ∀ x, ι x ≠ r) :
    (place S ι σ).R r = S.R r := by
  have h : ¬ ∃ x, ι x = r := fun ⟨x, hx⟩ => hr x hx
  simp [place, h]

/-- Placing a primitive's tapes over a placed bank places the updated bank. -/
theorem place_place (hι : Function.Injective ι) {s : ℕ} {slot : Fin s → Fin t}
    (hs : Function.Injective slot) (S : Stacks T A) (σ : Fin t → WTape) (τ : Fin s → WTape) :
    place (place S ι σ) (ι ∘ slot) τ = place S ι (upd σ slot τ) := by
  have hj : Function.Injective (ι ∘ slot) := hι.comp hs
  ext1
  · rfl
  · rfl
  all_goals
    funext r
    by_cases hr : ∃ x, ι x = r
    · obtain ⟨x, rfl⟩ := hr
      by_cases hx : ∃ i, slot i = x
      · obtain ⟨i, rfl⟩ := hx
        first
          | rw [show ι (slot i) = (ι ∘ slot) i from rfl, place_L_at hj, Function.comp_apply,
              place_L_at hι, upd_slot σ hs]
          | rw [show ι (slot i) = (ι ∘ slot) i from rfl, place_R_at hj, Function.comp_apply,
              place_R_at hι, upd_slot σ hs]
      · have hoff : ∀ i, (ι ∘ slot) i ≠ ι x := fun i h => hx ⟨i, hι h⟩
        have hno : ∀ i, slot i ≠ x := fun i h => hx ⟨i, h⟩
        first
          | rw [place_L_off _ _ hoff, place_L_at hι, place_L_at hι, upd_other σ slot τ x hno]
          | rw [place_R_off _ _ hoff, place_R_at hι, place_R_at hι, upd_other σ slot τ x hno]
    · have hoff : ∀ x, ι x ≠ r := fun x h => hr ⟨x, h⟩
      have hoff' : ∀ i, (ι ∘ slot) i ≠ r := fun i => hoff (slot i)
      first
        | rw [place_L_off _ _ hoff', place_L_off _ _ hoff, place_L_off _ _ hoff]
        | rw [place_R_off _ _ hoff', place_R_off _ _ hoff, place_R_off _ _ hoff]

theorem upd_comp_self {s : ℕ} {slot : Fin s → Fin t} (hs : Function.Injective slot)
    (σ : Fin t → WTape) : upd σ slot (σ ∘ slot) = σ := by
  funext x
  by_cases hx : ∃ i, slot i = x
  · obtain ⟨i, rfl⟩ := hx; rw [upd_slot σ hs]; rfl
  · exact upd_other σ slot _ x fun i h => hx ⟨i, h⟩

/-- One placed tape. -/
theorem place_one (S : Stacks T A) (j : Fin 1 → Fin T) (τ : Fin 1 → WTape) :
    place S j τ = { S with
      L := Function.update S.L (j 0) (lcells (τ 0).left)
      R := Function.update S.R (j 0) (cells (τ 0).right) } := by
  have hj : Function.Injective j := Function.injective_of_subsingleton j
  have hoff : ∀ {r}, r ≠ j 0 → ∀ x, j x ≠ r := fun hr x h => hr (by rw [← h, Subsingleton.elim x 0])
  ext1
  · rfl
  · rfl
  · funext r
    by_cases hr : r = j 0
    · subst hr; rw [place_L_at hj]; simp
    · rw [place_L_off _ _ (hoff hr)]; simp [hr]
  · funext r
    by_cases hr : r = j 0
    · subst hr; rw [place_R_at hj]; simp
    · rw [place_R_off _ _ (hoff hr)]; simp [hr]

end Place

/-! ### Implementations of primitives and compilation -/

section Compile

variable {A : ℕ}

/-- A host implementation of the primitive `M` with constant `C` on hosts with at least `n`
control states. -/
structure TImpl (C n : ℕ) (M : Prim A) : Type 1 where
  prog : {P : Type} → {T Q : ℕ} → {U : Type} → (Fin M.s → Fin T) → Pr P T Q A U
  spec : ∀ {P : Type} {T Q : ℕ} {U : Type} (body : P → Pr P T Q A U) (j : Fin M.s → Fin T),
    Function.Injective j → n ≤ Q → ∀ τ, M.pre τ → ∀ (v : HS T Q A U) (S : Stacks T A),
      ∃ v' n, v'.user = v.user ∧ n ≤ C * (M.cost τ + 1) ∧
        Exec body (prog j) (mk v (place S j τ)) n (mk v' (place S j (M.sem τ)))

variable {t : ℕ}

/-- Every primitive of a word program has a host implementation with constant `C` on hosts with
at least `n` control states. -/
inductive AllTM (C n : ℕ) : Cmd A t → Prop
  | prim {M : Prim A} {slot : Fin M.s → Fin t} {hinj : Function.Injective slot} :
      Nonempty (TImpl C n M) → AllTM C n (.prim M slot hinj)
  | seq {c d : Cmd A t} : AllTM C n c → AllTM C n d → AllTM C n (.seq c d)
  | loop {i : Fin t} {b : Cmd A t} : AllTM C n b → AllTM C n (.loop i b)
  | cond {i : Fin t} {c d : Cmd A t} : AllTM C n c → AllTM C n d → AllTM C n (.cond i c d)

variable {T Q : ℕ} {U P : Type}

/-- Record in `flag` whether the right stack of register `r` is nonempty and in `sym` its top. -/
def peekW (r : Fin T) : Act T Q A U :=
  .peek (.rt r) (fun v o => { v with flag := o.isSome, sym := o }) .done

open Classical in
/-- The host program of a word program on the registers `ι`. -/
noncomputable def tcompile (C n : ℕ) (ι : Fin t → Fin T) : Cmd A t → Pr P T Q A U
  | .prim M slot _ =>
      if h : Nonempty (TImpl C n M) then (Classical.choice h).prog (ι ∘ slot) else .act .done
  | .seq c d => .seq (tcompile C n ι c) (tcompile C n ι d)
  | .loop i b =>
      .seq (.act (peekW (ι i))) (.loop (·.flag) (.seq (tcompile C n ι b) (.act (peekW (ι i)))))
  | .cond i c d =>
      .seq (.act (peekW (ι i)))
        (.cond (fun v => decide (v.sym = some (bitSymbol true))) (tcompile C n ι c)
          (tcompile C n ι d))

variable (body : P → Pr P T Q A U)

theorem peekW_run (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekW r : Act T Q A U).run (mk v S) =
      mk { v with flag := (S.R r).head?.isSome, sym := (S.R r).head? } S := rfl

/-- **Compilation is correct.** -/
theorem tcompile_exec {C n : ℕ} (hC : 2 ≤ C) (hQ : n ≤ Q) {ι : Fin t → Fin T}
    (hι : Function.Injective ι) {c : Cmd A t} {σ σ' : Fin t → WTape} {k : ℕ}
    (h : Schoenhage.Exec c σ σ' k) (hc : AllTM C n c) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' m, v'.user = v.user ∧ m ≤ C * (k + 1) ∧
      Exec body (tcompile C n ι c) (mk v (place S ι σ)) m (mk v' (place S ι σ')) := by
  induction h generalizing v with
  | @prim M slot hinj σ hpre =>
    cases hc with
    | prim hM =>
      obtain ⟨v', n, hu, hn, he⟩ :=
        (Classical.choice hM).spec body (ι ∘ slot) (hι.comp hinj) hQ (σ ∘ slot) hpre v (place S ι σ)
      rw [place_place hι hinj, place_place hι hinj, upd_comp_self hinj] at he
      refine ⟨v', n, hu, hn, ?_⟩
      simpa only [tcompile, hM, ↓reduceDIte] using he
  | @seq c d σ σ₁ σ₂ k₁ k₂ h₁ h₂ ih₁ ih₂ =>
    cases hc with
    | seq hc hd =>
      obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := ih₁ hc v
      obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih₂ hd v₁
      refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
      rw [show C * (k₁ + 1 + k₂ + 1) = C * (k₁ + 1) + C * (k₂ + 1) by ring]
      omega
  | @loop_done i b σ hdone =>
    have hf : (place S ι σ).R (ι i) = [] := by rw [place_R_at hι, hdone]; rfl
    refine ⟨{ v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? },
      2, rfl, by omega, ?_⟩
    simp only [tcompile]
    exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.loop_false (by simp [peekW_run, hf]))
  | @loop_step i b σ σ₁ σ₂ k₁ k₂ hne h₁ h₂ ih₁ ih₂ =>
    cases hc with
    | loop hb =>
      have hf : ((place S ι σ).R (ι i)).head?.isSome = true := by
        rw [place_R_at hι, cells_head_isSome]; simpa using hne
      obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := ih₁ hb
        { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
      obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih₂ (.loop hb) v₁
      simp only [tcompile] at he₂
      cases he₂ with
      | @seq _ _ _ _ _ m n hp hl =>
        cases hp
        refine ⟨v₂, 1 + (n₁ + 1 + n + 1), hu₂.trans hu₁, ?_, ?_⟩
        · rw [show C * (k₁ + 2 + k₂ + 1) = C * (k₁ + 1) + C * (k₂ + 1) + C by ring]
          omega
        simp only [tcompile]
        exact Exec.seq (Exec.act (peekW (ι i)) _)
          (Exec.loop_true (by simpa [peekW_run] using hf)
            (Exec.seq he₁ (Exec.act (peekW (ι i)) _)) hl)
  | @cond_true i c d σ σ' k hone h₁ ih =>
    cases hc with
    | cond hc hd =>
      obtain ⟨v₁, n, hu, hn, he⟩ := ih hc
        { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
      have ht : ((place S ι σ).R (ι i)).head? = some (bitSymbol true) := by
        rw [place_R_at hι, cells_head_one]; exact hone
      refine ⟨v₁, 1 + (n + 1), hu, ?_, ?_⟩
      · rw [show C * (k + 1 + 1) = C * (k + 1) + C by ring]
        omega
      simp only [tcompile]
      exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.cond_true (by simp [peekW_run, ht]) he)
  | @cond_false i c d σ σ' k hone h₁ ih =>
    cases hc with
    | cond hc hd =>
      obtain ⟨v₁, n, hu, hn, he⟩ := ih hd
        { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
      have ht : ((place S ι σ).R (ι i)).head? ≠ some (bitSymbol true) := by
        rw [place_R_at hι, Ne, cells_head_one]; exact hone
      refine ⟨v₁, 1 + (n + 1), hu, ?_, ?_⟩
      · rw [show C * (k + 1 + 1) = C * (k + 1) + C by ring]
        omega
      simp only [tcompile]
      exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.cond_false (by simp [peekW_run, ht]) he)

/-- `tcompile_exec` for a run into a postcondition. -/
theorem tcompile_runs {C n : ℕ} (hC : 2 ≤ C) (hQ : n ≤ Q) {ι : Fin t → Fin T}
    (hι : Function.Injective ι) {c : Cmd A t} {σ : Fin t → WTape}
    {Post : (Fin t → WTape) → Prop} {B : ℕ} (h : Schoenhage.Runs c σ Post B) (hc : AllTM C n c)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ σ', Post σ' ∧ ∃ v' m, v'.user = v.user ∧ m ≤ C * (B + 1) ∧
      Exec body (tcompile C n ι c) (mk v (place S ι σ)) m (mk v' (place S ι σ')) := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  obtain ⟨v', n, hu, hn, he'⟩ := tcompile_exec body hC hQ hι he hc v S
  exact ⟨σ', hq, v', n, hu, hn.trans (Nat.mul_le_mul_left _ (by omega)), he'⟩

end Compile

/-! ### Moves on one register -/

section Moves

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether register `r`'s left stack has a top satisfying `p`. -/
def peekL (r : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .peek (.lt r) (fun v o => { v with flag := (o.map p).getD false }) .done

/-- Pop the left stack of register `r` onto its right stack. -/
def lrStep (r : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .pop (.lt r) (fun v o => { v with sym := o })
    (.push (.rt r) (fun v => v.sym.getD blank) (peekL r p))

/-- Move the left stack of register `r` onto its right stack while its top satisfies `p`. -/
def moveLR (r : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (peekL r p)) (.loop (·.flag) (.act (lrStep r p)))

theorem moveLR_loop (r : Fin T) (p : Fin (A + 4) → Bool) :
    ∀ (l rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ l, p x = true) → (rest.head?.map p).getD false = false → S.L r = l ++ rest →
      v.flag = ((l ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (lrStep r p))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            L := Function.update S.L r rest
            R := Function.update S.R r (l.reverse ++ S.R r) }) := by
  intro l
  induction l with
  | nil =>
    intro rest v S _ hrest hS hf
    refine ⟨v, rfl, ?_⟩
    have : ({ S with
        L := Function.update S.L r rest
        R := Function.update S.R r (([] : List (Fin (A + 4))).reverse ++ S.R r) } : Stacks T A) = S := by
      simp only [List.nil_append] at hS
      subst hS
      simp
    rw [this]
    exact .loop_false (by simpa [hrest] using hf)
  | cons e l ih =>
    intro rest v S hl hrest hS hf
    have he : p e = true := hl e List.mem_cons_self
    obtain ⟨v', hu, hx⟩ := ih rest { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
      { S with
        L := Function.update S.L r (l ++ rest)
        R := Function.update S.R r (e :: S.R r) }
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hrest (by simp) rfl
    refine ⟨v', hu, ?_⟩
    have hrun : (lrStep r p : Act T Q A U).run (mk v S) =
        mk { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
          { S with
            L := Function.update S.L r (l ++ rest)
            R := Function.update S.R r (e :: S.R r) } := by
      simp [lrStep, peekL, Action.run, hS, update_lt, update_rt]
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hS, he] using hf)
      (hrun ▸ Exec.act (body := body) (lrStep r p) (mk v S)) hx) (by simp; ring) ?_
    congr 2 <;> simp

theorem moveLR_exec (r : Fin T) (p : Fin (A + 4) → Bool) (l rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hl : ∀ x ∈ l, p x = true)
    (hrest : (rest.head?.map p).getD false = false) (hS : S.L r = l ++ rest) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveLR r p) (mk v S) (2 * l.length + 2)
        (mk v' { S with
          L := Function.update S.L r rest
          R := Function.update S.R r (l.reverse ++ S.R r) }) := by
  obtain ⟨v', hu, he⟩ := moveLR_loop body r p l rest
    { v with flag := ((S.L r).head?.map p).getD false } S hl hrest hS (by rw [hS])
  exact ⟨v', hu, Exec.cast (Exec.seq (Exec.act (body := body) (peekL r p) (mk v S)) he) (by ring) rfl⟩

/-- Empty the right stack of register `r`. -/
def dropR (r : Fin T) : Pr P T Q A U :=
  whileR r (.pop (.rt r) (fun v _ => v) (peekR r))

theorem dropR_loop (r : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    S.R r = l → v.flag = l.head?.isSome →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (.pop (.rt r) (fun v _ => v) (peekR r)))) (mk v S)
        (2 * l.length + 1) (mk v' { S with R := Function.update S.R r [] }) := by
  intro l
  induction l with
  | nil =>
    intro v S hS hf
    refine ⟨v, rfl, ?_⟩
    have : ({ S with R := Function.update S.R r [] } : Stacks T A) = S := by rw [← hS]; simp
    rw [this]
    exact .loop_false (by simpa using hf)
  | cons e l ih =>
    intro v S hS hf
    obtain ⟨v', hu, hx⟩ := ih { v with flag := l.head?.isSome }
      { S with R := Function.update S.R r l } (by simp) rfl
    refine ⟨v', hu, ?_⟩
    have hrun : (Action.pop (.rt r) (fun v _ => v) (peekR r) : Act T Q A U).run (mk v S) =
        mk { v with flag := l.head?.isSome } { S with R := Function.update S.R r l } := by
      simp [peekR, Action.run, hS, update_rt]
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
      (hrun ▸ Exec.act (body := body) _ (mk v S)) hx) (by simp; ring) ?_
    congr 2; simp

theorem dropR_exec (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (dropR r) (mk v S) (2 * (S.R r).length + 2)
        (mk v' { S with R := Function.update S.R r [] }) := by
  obtain ⟨v', hu, he⟩ := dropR_loop body r (S.R r) { v with flag := (S.R r).head?.isSome } S rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run r v S ▸ Exec.act (body := body) (peekR r) (mk v S)) he)
    (by ring) rfl⟩

/-- Push `l` onto the left stack of register `r`, its last symbol on top. -/
def pushL (r : Fin T) : List (Fin (A + 4)) → Act T Q A U
  | [] => .done
  | x :: xs => .push (.lt r) (fun _ => x) (pushL r xs)

theorem pushL_run (r : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    (pushL r l).run (mk v S) = mk v { S with L := Function.update S.L r (l.reverse ++ S.L r) }
  | [], v, S => by simp [pushL]
  | x :: xs, v, S => by
    simp only [pushL, Action.run, mk_var, mk_stk, get_lt, update_lt, store_mk]
    rw [pushL_run r xs]
    congr 2
    simp

/-- Pop the left stack of register `r` onto its right stack once. -/
def popLR (r : Fin T) : Act T Q A U :=
  .pop (.lt r) (fun v o => { v with sym := o }) (.push (.rt r) (fun v => v.sym.getD blank) .done)

end Moves

/-! ### The primitives rewind, back, clear and emit -/

section Prims

variable {A : ℕ}

theorem bitSymbol_ne_sep (b : Bool) : bitSymbol (a := A) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator]

theorem two_le_mul {C x : ℕ} (hC : 2 ≤ C) : 2 * x ≤ C * x := Nat.mul_le_mul_right x hC

/-- Rewind on host stacks: the left stack onto the right stack. -/
noncomputable def rewindImpl (C n : ℕ) (hC : 2 ≤ C) : TImpl C n (Schoenhage.Rewind.prim (a := A)) where
  prog j := moveLR (j 0) (fun _ => true)
  spec body j _ _ τ _ v S := by
    obtain ⟨v', hu, he⟩ := moveLR_exec body (j 0) (fun _ => true) (lcells (τ 0).left) [] v
      (place S j τ) (by simp) rfl (by rw [place_one]; simp)
    refine ⟨v', _, hu, ?_, he.cast rfl ?_⟩
    · have := two_le_mul (x := clen (τ 0).left + 2 + 1) hC
      simp only [length_lcells]
      omega
    · congr 1
      simp only [place_one]
      congr 1
      · simp [lcells]
      · simp [reverse_lcells, cells_append']

/-- Back on host stacks: the separator and then the bits of the previous word onto the right
stack. -/
noncomputable def backImpl (C n : ℕ) (hC : 2 ≤ C) : TImpl C n (Schoenhage.Back.prim (a := A)) where
  prog j := .seq (.act (popLR (j 0))) (moveLR (j 0) (fun x => decide (x ≠ separator)))
  spec body j _ _ τ hpre v S := by
    obtain ⟨u, L, hL⟩ : ∃ u L, (τ 0).left = u :: L := by
      rcases h : (τ 0).left with _ | ⟨u, L⟩
      · exact absurd h hpre
      · exact ⟨u, L, rfl⟩
    set S₀ := place S j τ
    have hrun : (popLR (j 0) : Act _ _ A _).run (mk v S₀) =
        mk { v with sym := some separator }
          { S₀ with
            L := Function.update S₀.L (j 0) (u.reverse.map bitSymbol ++ lcells L)
            R := Function.update S₀.R (j 0) (separator :: S₀.R (j 0)) } := by
      have : S₀.L (j 0) = separator :: (u.reverse.map bitSymbol ++ lcells L) := by
        simp [S₀, place_one, hL, lcells]
      simp [popLR, Action.run, this, update_lt, update_rt]
    obtain ⟨v', hu, he⟩ := moveLR_exec body (j 0) (fun x => decide (x ≠ separator))
      (u.reverse.map bitSymbol) (lcells L) { v with sym := some separator }
      { S₀ with
        L := Function.update S₀.L (j 0) (u.reverse.map bitSymbol ++ lcells L)
        R := Function.update S₀.R (j 0) (separator :: S₀.R (j 0)) }
      (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; simpa using bitSymbol_ne_sep b)
      (by cases L <;> simp [lcells]) (by simp)
    refine ⟨v', _, hu, ?_, (Exec.seq (hrun ▸ Exec.act _ _) he).cast rfl ?_⟩
    · have := two_le_mul (x := ((τ 0).left.headD []).length + 3 + 1) hC
      simp only [hL, List.headD_cons, List.length_map, List.length_reverse] at this ⊢
      omega
    · congr 1
      simp only [S₀, place_one]
      congr 1
      · simp [hL]
      · simp [hL, cells_cons', List.map_reverse]

/-- Clear on host stacks: rewind, then empty the right stack. -/
noncomputable def clearImpl (C n : ℕ) (hC : 2 ≤ C) : TImpl C n (Schoenhage.Clear.prim (a := A)) where
  prog j := .seq (moveLR (j 0) (fun _ => true)) (dropR (j 0))
  spec body j _ _ τ _ v S := by
    obtain ⟨v₁, hu₁, he₁⟩ := moveLR_exec body (j 0) (fun _ => true) (lcells (τ 0).left) [] v
      (place S j τ) (by simp) rfl (by rw [place_one]; simp)
    obtain ⟨v₂, hu₂, he₂⟩ := dropR_exec body (j 0) v₁
      { place S j τ with
        L := Function.update (place S j τ).L (j 0) []
        R := Function.update (place S j τ).R (j 0)
          ((lcells (τ 0).left).reverse ++ (place S j τ).R (j 0)) }
    refine ⟨v₂, _, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
    · have := two_le_mul (x := 2 * clen (τ 0).words + 2 + 1) hC
      simp only [place_one, Function.update_self, length_lcells, List.length_append,
        List.length_reverse, Schoenhage.length_cells, WTape.words, Schoenhage.clen_append,
        Schoenhage.clen_reverse] at this ⊢
      omega
    · congr 1
      simp only [place_one]
      congr 1
      · simp [lcells]
      · simp [cells]

/-- Emit on host stacks: the cells of the words onto the left stack, in one step. -/
noncomputable def emitImpl (C n : ℕ) (hC : 2 ≤ C) (ws : List (List Bool)) :
    TImpl C n (Schoenhage.Emit.prim (a := A) ws) where
  prog j := .act (pushL (j 0) (cells ws))
  spec body j _ _ τ hpre v S := by
    refine ⟨v, 1, rfl, Nat.mul_pos (by omega) (by omega), ?_⟩
    refine (Exec.act (body := body) _ _).cast rfl ?_
    rw [pushL_run]
    congr 1
    simp only [place_one]
    congr 1
    · simp [lcells_append, lcells_reverse]
    · have hr : (τ 0).right = [] := hpre
      simp [hr]

variable {t : ℕ}

theorem allTM_rewind {C : ℕ} (n : ℕ) (hC : 2 ≤ C) (i : Fin t) :
    AllTM C n (Schoenhage.rewind (a := A) i) :=
  .prim ⟨rewindImpl C n hC⟩

theorem allTM_back {C : ℕ} (n : ℕ) (hC : 2 ≤ C) (i : Fin t) : AllTM C n (Schoenhage.back (a := A) i) :=
  .prim ⟨backImpl C n hC⟩

theorem allTM_clear {C : ℕ} (n : ℕ) (hC : 2 ≤ C) (i : Fin t) :
    AllTM C n (Schoenhage.clear (a := A) i) :=
  .prim ⟨clearImpl C n hC⟩

theorem allTM_emit {C : ℕ} (n : ℕ) (hC : 2 ≤ C) (ws : List (List Bool)) (i : Fin t) :
    AllTM C n (Schoenhage.emit (a := A) ws i) :=
  .prim ⟨emitImpl C n hC ws⟩

end Prims

end IntegerMultBounds.MathlibTM2.Host.WordCmd
