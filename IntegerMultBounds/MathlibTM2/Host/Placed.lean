module

public import IntegerMultBounds.MathlibTM2.Host.Core
public import IntegerMultBounds.Machine.PlacementBank

/-!
# Placed subroutines on the host

A program placed on a family of host tapes (`Placement.placed`) writes back the scanned symbol and
keeps its head still on every other tape (`placed_idle`). `foreign_exec_frame` strengthens
`foreign_exec` by such idle tapes: the left stack of an idle tape is unchanged, and its right stack
is unchanged or, when it was empty, becomes `[blank]` (`padR`). On a nonempty right stack the
simulation therefore changes nothing (`foreign_exec_frame_ne_nil`).

`markList` and `dropList` push a blank onto, and pop, the right stacks of a list of tapes; they
make the right stacks of idle tapes nonempty for the duration of a run.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


variable {T Q A : ℕ} {U : Type}

/-! ### Idle tapes -/

/-- Every transition of `M` writes back the scanned symbol and stays on each tape in `I`. -/
def Idle (M : Program T Q A) (I : Fin T → Prop) : Prop :=
  ∀ st sym st' act, M.transition st sym = some (st', act) → ∀ i, I i → act i = (sym i, .stay)

/-- Every transition of a placed program writes back the scanned symbol and stays on every tape
outside the placement. -/
theorem placed_idle {s u t q a : ℕ} (M : Program s q a) (e : Fin (s + u) ≃ Fin t) :
    Idle (Placement.placed M e) (fun x => ∀ i, e (Fin.castAdd u i) ≠ x) := by
  intro st sym st' act h x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [Placement.placed, reindex, extend, Option.map_map] at h
  obtain ⟨⟨st₀, act₀⟩, -, h₂⟩ := Option.map_eq_some_iff.1 h
  simp only [Function.comp_apply, Prod.mk.injEq] at h₂
  obtain ⟨-, rfl⟩ := h₂
  revert hx
  refine Fin.addCases (fun i hx => ?_) (fun j _ => ?_) y
  · exact absurd rfl (hx i)
  · simp

/-- `placed_idle` for the placement of an injective tape family. -/
theorem placed_idle_injective {s u t q a : ℕ} (M : Program s q a) (ι : Fin s → Fin t)
    (hι : Function.Injective ι) (hsize : s + u = t) :
    Idle (Placement.placed M (InjectivePlacement.placement ι hι hsize)) (fun x => ∀ i, ι i ≠ x) :=
  fun st sym st' act h x hx => placed_idle M _ st sym st' act h x
    (fun i => by rw [InjectivePlacement.active_slot]; exact hx i)

/-- The right stack after a transition that writes back the scanned symbol and stays. -/
def padR (r : List (Fin (A + 4))) : List (Fin (A + 4)) := r.head?.getD blank :: r.tail

@[simp] lemma padR_nil : padR ([] : List (Fin (A + 4))) = [blank] := rfl

lemma padR_of_ne_nil {r : List (Fin (A + 4))} (h : r ≠ []) : padR r = r := by
  cases r with
  | nil => exact absurd rfl h
  | cons x r => rfl

@[simp] lemma padR_padR (r : List (Fin (A + 4))) : padR (padR r) = padR r := rfl

/-! ### Simulation with idle tapes -/

variable {P : Type} (body : P → Pr P T Q A U)

/-- `sim_loop`, with idle tapes: their left stacks are unchanged, their right stacks unchanged or
padded. -/
theorem sim_loop_frame (M : Program T Q A) {I : Fin T → Prop} (hI : Idle M I) :
    ∀ (k : ℕ) (c : Config T Q A) (v : HS T Q A U) (S : Stacks T A),
    Rep c S.L S.R → v.st = c.state → v.flag = true →
    ∀ cf, run M k c = some cf → step M cf = none →
    ∃ v' S', Exec body (.loop (·.flag) (simIter M)) (mk v S) (k * (T + 5) + 5) (mk v' S') ∧
      Rep cf S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      (∀ i, (S'.L i).length + (S'.R i).length ≤ (S.L i).length + (S.R i).length + 2 * k) ∧
      ∀ i, I i → S'.L i = S.L i ∧ (S'.R i = S.R i ∨ S'.R i = padR (S.R i)) := by
  intro k
  induction k with
  | zero =>
      intro c v S hrep hst hfl cf hrun hstep
      simp only [run, Option.some.injEq] at hrun
      subst hrun
      have ht : M.transition c.state (fun i => c.tape i (c.head i)) = none := by
        unfold step at hstep
        split at hstep
        · assumption
        · simp at hstep
      obtain ⟨v', h₁, h₂, h₃, he⟩ := simIter_halt (body := body) M hrep hst ht
      refine ⟨v', S, ?_, hrep, h₁, rfl, rfl, fun i => by omega, fun i _ => ⟨rfl, .inl rfl⟩⟩
      have := Exec.loop_true (body := body) (f := (·.flag)) hfl he (.loop_false (by simpa using h₂))
      simpa using this
  | succ k ih =>
      intro c v S hrep hst hfl cf hrun hstep
      simp only [run] at hrun
      cases hs : step M c with
      | none => simp [hs] at hrun
      | some c₁ =>
          rw [hs, Option.bind_some] at hrun
          obtain ⟨st', act, ht⟩ : ∃ st' act,
              M.transition c.state (fun i => c.tape i (c.head i)) = some (st', act) := by
            unfold step at hs
            split at hs
            · simp at hs
            · exact ⟨_, _, by assumption⟩
          obtain ⟨c', hc', hcs, hrep'⟩ := rep_step hrep ht
          rw [hs, Option.some.injEq] at hc'
          subst hc'
          obtain ⟨v₁, h₁, h₂, h₃, he⟩ := simIter_step (body := body) M hrep hst ht
          obtain ⟨v', S', he', hrep'', hl, hin, ho, hsz, hfr⟩ :=
            ih c₁ v₁ { S with
              L := newL S act
              R := newR S act } hrep' (by rw [h₃, hcs]) (by rw [h₂, hfl]) cf hrun hstep
          refine ⟨v', S', ?_, hrep'', hl.trans h₁, hin, ho, fun i => ?_, fun i hi => ?_⟩
          · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hfl he he') (by ring) rfl
          · have h₄ := hsz i
            have h₅ := stepStacks_length (S.L i) (S.R i) (act i).1 (act i).2
            simp only [newL, newR] at h₄ ⊢
            omega
          · have hact := hI _ _ _ _ ht i hi
            have hsc := rep_scan hrep i
            obtain ⟨hL', hR'⟩ := hfr i hi
            have hL1 : newL S act i = S.L i := by simp [newL, hact, stepStacks]
            have hR1 : newR S act i = padR (S.R i) := by
              simp [newR, hact, stepStacks, padR, hsc]
            simp only at hL' hR'
            rw [hL1] at hL'
            rw [hR1, padR_padR] at hR'
            exact ⟨hL', .inr (hR'.elim id id)⟩

/-- `foreign_exec`, with idle tapes: their left stacks are unchanged, their right stacks unchanged
or padded. -/
theorem foreign_exec_frame (M : Program T Q A) {I : Fin T → Prop} (hI : Idle M I)
    {pre post : TapePred T A} {k : ℕ}
    (h : HoareTime M pre post k) (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧ S'.inp = S.inp ∧
      S'.out = S.out ∧
      (∀ i, (S'.L i).length + (S'.R i).length ≤ (S.L i).length + (S.R i).length + 2 * k) ∧
      (∀ i, I i → S'.L i = S.L i ∧ (S'.R i = S.R i ∨ S'.R i = padR (S.R i))) ∧
      ∃ m ≤ k * (T + 5) + 6, Exec body (foreign M) (mk v S) m (mk v' S') := by
  obtain ⟨kk, c, hkk, hrun, hstep, hpost⟩ := h w hw
  obtain ⟨v', S', he, hrep', hu, hin, ho, hsz, hfr⟩ :=
    sim_loop_frame body M hI kk (w.start M) { v with flag := true, st := M.start } S hrep rfl rfl
      c hrun hstep
  refine ⟨v', S', c.tapes, hpost, hrep', hu, hin, ho, fun i => ?_, hfr, _, ?_,
    Exec.seq (Exec.act (body := body) _ (mk v S)) he⟩
  · have := hsz i; omega
  · have : kk * (T + 5) ≤ k * (T + 5) := Nat.mul_le_mul_right _ hkk
    omega

/-- An idle tape with a nonempty right stack keeps both stacks exactly. -/
lemma idle_stacks_eq {L L' R R' : List (Fin (A + 4))} (h : L' = L ∧ (R' = R ∨ R' = padR R))
    (hR : R ≠ []) : L' = L ∧ R' = R :=
  ⟨h.1, h.2.elim id (fun h' => h'.trans (padR_of_ne_nil hR))⟩

/-! ### Marking right stacks -/

/-- Run `a i` for each tape `i` of a list, where `a i` maps the right stack of tape `i` by `g`. -/
theorem eachR_exec (a : Fin T → Act T Q A U) (g : List (Fin (A + 4)) → List (Fin (A + 4)))
    (ha : ∀ i v S, (a i).run (mk v S) = mk v { S with R := Function.update S.R i (g (S.R i)) }) :
    ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      Exec body (Prog.seqList (l.map fun i => .act (a i))) (mk v S) (l.length + 1)
        (mk v { S with R := fun i => if i ∈ l then g (S.R i) else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      have : ({ S with R := fun i => if i ∈ ([] : List (Fin T)) then g (S.R i) else S.R i } :
          Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      have he₂ := ih hnd.2 v { S with R := Function.update S.R i (g (S.R i)) }
      refine Exec.cast (Exec.seq ((ha i v S) ▸ Exec.act (body := body) (a i) (mk v S)) he₂)
        (by simp; ring) ?_
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj; simp [hnd.1]
      · simp [hj]

/-- Push a blank onto the right stack of tape `i`. -/
def markStep (i : Fin T) : Act T Q A U := .push (.rt i) (fun _ => blank) .done

/-- Pop the right stack of tape `i`, discarding the symbol. -/
def dropStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) .done

/-- Push a blank onto the right stack of each tape of a list. -/
def markList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map fun i => .act (markStep i))

/-- Pop the right stack of each tape of a list. -/
def dropList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map fun i => .act (dropStep i))

theorem markList_exec (l : List (Fin T)) (hl : l.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (markList l) (mk v S) (l.length + 1)
      (mk v { S with R := fun i => if i ∈ l then blank :: S.R i else S.R i }) :=
  eachR_exec body markStep (fun r => blank :: r)
    (fun i v S => by simp [markStep, Action.run, update_rt]) l hl v S

theorem dropList_exec (l : List (Fin T)) (hl : l.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (dropList l) (mk v S) (l.length + 1)
      (mk v { S with R := fun i => if i ∈ l then (S.R i).tail else S.R i }) :=
  eachR_exec body dropStep List.tail
    (fun i v S => by simp [dropStep, Action.run, update_rt]) l hl v S

/-! ### Tapes outside a family -/

/-- The tapes outside the range of `ι`, in increasing order. -/
def unplaced {s : ℕ} (ι : Fin s → Fin T) : List (Fin T) :=
  (List.finRange T).filter fun x => decide (∀ j, ι j ≠ x)

lemma mem_unplaced {s : ℕ} (ι : Fin s → Fin T) (x : Fin T) :
    x ∈ unplaced ι ↔ ∀ j, ι j ≠ x := by
  simp [unplaced, List.mem_filter, List.mem_finRange]

lemma unplaced_nodup {s : ℕ} (ι : Fin s → Fin T) : (unplaced ι).Nodup :=
  (List.nodup_finRange T).filter _

lemma unplaced_length_le {s : ℕ} (ι : Fin s → Fin T) : (unplaced ι).length ≤ T :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

end IntegerMultBounds.MathlibTM2.Host
