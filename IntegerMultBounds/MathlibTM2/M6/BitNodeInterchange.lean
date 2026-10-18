module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeIdle

/-!
# The five-class node is the parent interchange

**`runNode_interchange`**: on arbitrary dirty streams of all `5W = 142080` roles, the five-class
node program `nodeProgram` changes every role by `D_1`, the exchange of the two address halves.

The proof keeps the frame bookkeeping `Inv` through the 28 pieces before the final exchange
(`prefix_inv`): the stage pieces, remainder children and bridges each preserve it, with the
logical streams following the recipe on banks. The recipe is the identity on banks
(`Nine.recipe_runBank`), so the logical streams return (`logicalRun_schedule`), and every role
ends in its exchanged frame: side zero from the line to its complement, side one from zero to
the full frame. Both are `D_1` after the initial frame.

**Scope: an upstream-conditional certificate.** The pieces are role-level operators on streams
over rational address pairs: each frame change is an exact partial swap, and the stage routes and
helper charts are exact coordinate changes. The theorem is the semantics of upstream's idealized
PR589 node. A tape machine inherits it only through a realization of these pieces at upstream's
prices, and none is known: on the H-before-D tape the routes cost interchanges (`M6/DESIGN.md`,
"Realizability of the PR589 accounting").
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitSchedule
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-! ### Prefixes -/

/-- The logical streams after a list of schedule entries. -/
def logicalRun (es : List Entry) (L : State) : State := es.foldl (fun L e => logicalStep e L) L

theorem nodeProgram_at :
    (∀ s : Fin 9, nodeProgram.getD (stagePos s.val) .exchangeSides = .stage s) ∧
    (∀ i < 10, nodeProgram.getD (idlePos i) .exchangeSides = .remainder i) ∧
    (∀ τ < 29, ∀ x, bridgeAt τ = some x → nodeProgram.getD τ .exchangeSides = .bridge x.1 x.2) ∧
    nodeProgram.getD 28 .exchangeSides = .exchangeSides := by
  decide +kernel

theorem schedule_length : (schedule 4).length = 29 := by
  decide +kernel

theorem foldl_take_succ {α β : Type*} (l : List α) (f : β → α → β) (x : β) (d : α) (τ : ℕ)
    (hτ : τ < l.length) : (l.take (τ + 1)).foldl f x = f ((l.take τ).foldl f x) (l.getD τ d) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hτ, Option.toList_some,
    List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hτ,
    Option.getD_some]

/-- The logical streams the node starts from: each role decoded from its initial frame. -/
noncomputable def initialLogical (X : State) : State := fun ρ => along (exchange (frameAt 0 ρ)) (X ρ)

theorem frameAt_zero (ρ : Role) : frameAt 0 ρ = sidePart ρ := by
  rw [frameAt, pendingSum_none 0 ρ (fun σ hσ _ => (start_facts.2 σ hσ)), start_facts.1 _
    (by have := ρ.bank.isLt; omega), Nat.mul_zero, span_self, add_zero, add_zero]

theorem sidePart_idem (ρ : Role) : sidePart ρ * sidePart ρ = sidePart ρ := by
  unfold sidePart
  split_ifs
  · rw [PortCertificate.linePart, fromBlocks_multiply, PortCertificate.lineProj_mul_self (port_ok ρ)]
    simp
  · simp

theorem inv_zero (X : State) : Inv 0 X (initialLogical X) := by
  intro ρ
  rw [initialLogical, ← along_mul, exchange_mul_self (by rw [frameAt_zero]; exact sidePart_idem ρ),
    along_one]

/-- The bookkeeping holds after every piece before the exchange. -/
theorem prefix_inv (X : State) : ∀ τ ≤ 28,
    Inv τ (runPieces (nodeProgram.take τ) X) (logicalRun ((schedule 4).take τ) (initialLogical X))
  | 0, _ => by simpa [runPieces, logicalRun] using inv_zero X
  | τ + 1, hτ => by
    have ih := prefix_inv X τ (by omega)
    rw [runPieces, foldl_take_succ _ _ _ .exchangeSides τ (by rw [show nodeProgram.length = 29 from rfl]; omega),
      logicalRun, foldl_take_succ _ _ _ .exchange τ (by rw [schedule_length]; omega)]
    have hentry : (schedule 4).getD τ .exchange = entryAt τ := rfl
    rw [hentry]
    rcases entry_kinds τ (by omega) with ⟨s, hs, rfl⟩ | ⟨i, hi, rfl⟩ | hb | h28
    · rw [nodeProgram_at.1 ⟨s, hs⟩, (positions_check.1 s hs)]
      exact sweep_step ⟨s, hs⟩ _ _ ih
    · rw [nodeProgram_at.2.1 i hi, (positions_check.2 i hi)]
      exact idle_step i hi _ _ ih
    · obtain ⟨⟨d, s⟩, hx⟩ := Option.isSome_iff_exists.mp hb
      rw [nodeProgram_at.2.2.1 τ (by omega) _ hx, bridge_entries τ (by omega) d s hx]
      exact bridge_step τ (by omega) d s hx _ _ ih
    · omega

/-! ### The logical streams return -/

/-- A bank vector of logical streams. -/
def bankVec (L : State) (r : Fin 32) (t : Fin 111) (g : Fin 5) : ℕ → Stream :=
  fun b => if h : b < 8 then L ⟨r, ⟨b, h⟩, t, g⟩ else 0

/-- The schedule entry that carries a recipe event. -/
def mainEntry : Event → Entry
  | .sweep s p _ => .sweep s p
  | .bridge d s _ => .bridge d s
  | .exchange => .exchange

def isIdle : Entry → Bool
  | .idle _ _ => true
  | _ => false

/-- The recipe-event properties the bank transport uses. -/
def shapeOk : Event → Bool
  | .sweep s p rev => (rev == decide (s % 2 = 1)) && decide (p < 4)
  | .bridge d s _ => decide (d < 4) && decide (s < 4) && decide (d ≠ s)
  | .exchange => true

/-- An event's schedule entries are its main entry followed by idles. -/
def entriesOk (e : Event) : Bool :=
  decide ((entriesOf 4 e).head? = some (mainEntry e)) && (entriesOf 4 e).tail.all isIdle

theorem recipe_ok : ∀ e ∈ recipe 4, entriesOk e = true ∧ shapeOk e = true := by
  decide +kernel

theorem logicalRun_idles (es : List Entry) (hes : es.all isIdle = true) (L : State) :
    logicalRun es L = L := by
  induction es generalizing L with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hes
    rcases e with _ | _ | _ | _ <;> simp_all [logicalRun, isIdle, logicalStep]

theorem logicalRun_entries (e : Event) (he : e ∈ recipe 4) (L : State) :
    logicalRun (entriesOf 4 e) L = logicalStep (mainEntry e) L := by
  obtain ⟨hok, -⟩ := recipe_ok e he
  simp only [entriesOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hh, ht⟩ := hok
  cases hl : entriesOf 4 e with
  | nil => simp [hl] at hh
  | cons x rest =>
    rw [hl] at hh ht
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.tail_cons] at ht
    rw [logicalRun, List.foldl_cons, hh]
    exact logicalRun_idles rest ht _

theorem withBank_bankVec (L : State) (ρ : Role) (b : ℕ) (hb : b < 8) :
    L (withBank ρ b) = bankVec L ρ.replica ρ.port ρ.cls b := by
  simp [bankVec, hb, withBank, Nat.mod_eq_of_lt hb]

theorem logicalStep_bank (e : Event) (hshape : shapeOk e = true) (L : State) (ρ : Role) :
    logicalStep (mainEntry e) L ρ = stepBank 4 (bankVec L ρ.replica ρ.port ρ.cls) e ρ.bank.val := by
  have hself : L ρ = bankVec L ρ.replica ρ.port ρ.cls ρ.bank.val := by
    simp only [bankVec, dite_eq_left ρ.bank.isLt]
  have hw := withBank_bankVec L ρ
  have hb := ρ.bank.isLt
  rcases e with ⟨s, p, rev⟩ | ⟨d, s, c⟩ | _
  · simp only [shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
    obtain ⟨rfl, hp⟩ := hshape
    simp only [mainEntry, logicalStep, stepBank]
    generalize bankVec L ρ.replica ρ.port ρ.cls = x at hself hw ⊢
    generalize ρ.bank.val = b at hself hb ⊢
    by_cases hodd : s % 2 = 1
    · rw [ite_eq_left hodd, ite_eq_left (decide_eq_true hodd), Function.update_apply]
      split_ifs with h1
      · subst h1
        rw [hself, hw _ (by omega)]
      · exact hself
    · rw [ite_eq_right hodd, ite_eq_right (show ¬decide (s % 2 = 1) = true by simpa using hodd),
        Function.update_apply]
      split_ifs with h1
      · subst h1
        rw [hself, hw _ (by omega)]
      · exact hself
  · simp only [shapeOk, Bool.and_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨⟨hd, hs⟩, hds⟩ := hshape
    simp only [mainEntry, logicalStep, stepBank, Function.update_apply]
    generalize bankVec L ρ.replica ρ.port ρ.cls = x at hself hw ⊢
    generalize ρ.bank.val = b at hself hb ⊢
    split_ifs <;> first | omega | exact hself | (subst_vars; rw [hself, hw _ (by omega)])
  · have h8 : ρ.bank.val < 2 * 4 := hb
    simp only [mainEntry, logicalStep, stepBank, otherSide, h8, ↓reduceIte]
    exact hw _ (by split_ifs <;> omega)

theorem bankVec_step (e : Event) (he : e ∈ recipe 4) (L : State) (r : Fin 32) (t : Fin 111)
    (g : Fin 5) : bankVec (logicalStep (mainEntry e) L) r t g = stepBank 4 (bankVec L r t g) e := by
  have hshape := (recipe_ok e he).2
  funext b
  by_cases hb : b < 8
  · rw [show bankVec (logicalStep (mainEntry e) L) r t g b =
        logicalStep (mainEntry e) L ⟨r, ⟨b, hb⟩, t, g⟩ by simp only [bankVec, dite_eq_left hb]]
    exact logicalStep_bank e hshape L ⟨r, ⟨b, hb⟩, t, g⟩
  · have hx : bankVec L r t g b = 0 := by simp only [bankVec, dite_eq_right hb]
    rw [show bankVec (logicalStep (mainEntry e) L) r t g b = 0 by simp only [bankVec, dite_eq_right hb]]
    rcases e with ⟨s, p, rev⟩ | ⟨d, s, c⟩ | _
    · simp only [shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
      obtain ⟨-, hp⟩ := hshape
      simp only [stepBank]
      split_ifs <;> rw [Function.update_of_ne (by omega), hx]
    · simp only [shapeOk, Bool.and_eq_true, decide_eq_true_eq] at hshape
      obtain ⟨⟨hd, hs⟩, -⟩ := hshape
      simp only [stepBank, Function.update_apply]
      split_ifs <;> first | omega | exact hx.symm
    · simp only [stepBank]
      split_ifs <;> first | omega | exact hx.symm

theorem logicalRun_schedule (L : State) : logicalRun (schedule 4) L = L := by
  have hsplit : ∀ (es : List Event), (∀ e ∈ es, e ∈ recipe 4) → ∀ L : State, ∀ r t g,
      bankVec (logicalRun (es.flatMap (entriesOf 4)) L) r t g = es.foldl (stepBank 4) (bankVec L r t g) := by
    intro es hes
    induction es with
    | nil => intro L r t g; rfl
    | cons e rest ih =>
      intro L r t g
      rw [List.flatMap_cons, logicalRun, List.foldl_append, ← logicalRun, ← logicalRun,
        logicalRun_entries e (hes e List.mem_cons_self), List.foldl_cons,
        ← bankVec_step e (hes e List.mem_cons_self)]
      exact ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) _ r t g
  funext ρ
  have h := hsplit (recipe 4) (fun e he => he) L ρ.replica ρ.port ρ.cls
  rw [← runBank, recipe_runBank] at h
  have := congrFun h ρ.bank.val
  simp only [bankVec, dite_eq_left ρ.bank.isLt] at this
  rw [schedule]
  exact this

/-! ### The interchange -/

theorem otherSide_facts (ρ : Role) : (otherSide ρ).port = ρ.port ∧
    (otherSide ρ).bank.val % 2 = 1 - ρ.bank.val % 2 ∧ (otherSide ρ).bank.val / 2 = ρ.bank.val / 2 := by
  have := ρ.bank.isLt
  simp only [otherSide, withBank]
  split_ifs <;> simp <;> omega

theorem final_frame (ρ : Role) :
    exchange (frameAt 0 ρ) * exchange (frameAt 28 (otherSide ρ)) = exchange 1 := by
  have hq : (otherSide ρ).bank.val / 2 < 4 := by have := (otherSide ρ).bank.isLt; omega
  obtain ⟨hp, hs, -⟩ := otherSide_facts ρ
  have hc := port_ok ρ
  rw [frameAt_zero, frameAt_level 28 _ (fun σ hσ _ => exchange_facts.2 σ hσ), exchange_facts.1 _ hq,
    hp, hs]
  unfold sidePart
  by_cases h0 : ρ.bank.val % 2 = 0
  · have hls : (port ρ.port.val).linePart = (port ρ.port.val).sourceFrame 0 := rfl
    rw [ite_eq_left h0, ite_eq_right (by omega), PortCertificate.targetFrame_nine, hls,
      exchange_mul_of_orthogonal (by rw [mul_sub, mul_one, sourceFrame_idem _ hc, sub_self]),
      add_sub_cancel]
  · rw [ite_eq_right h0, ite_eq_left (by omega), PortCertificate.sourceFrame_nine, exchange_zero, Matrix.one_mul]

/-- **The five-class node is the parent interchange.** On arbitrary dirty streams of all
`5W = 142080` roles, the node program changes every role by the exchange `D_1` of its two
address halves. The program's pieces are upstream's idealized operators (module docstring), so
this is the idealized node's semantics. -/
theorem runNode_interchange (X : State) (ρ : Role) : runNode X ρ = along (exchange 1) (X ρ) := by
  have hinv := prefix_inv X 28 le_rfl
  have hrun : runNode X = (Piece.exchangeSides).run (runPieces (nodeProgram.take 28) X) := by
    have h := foldl_take_succ nodeProgram (fun Y (p : Piece) => p.run Y) X Piece.exchangeSides 28
      (by decide)
    rw [nodeProgram_at.2.2.2, List.take_of_length_le (by decide)] at h
    rw [runNode, runPieces, runPieces, h]
  have hlog : logicalRun (schedule 4) (initialLogical X) =
      logicalStep .exchange (logicalRun ((schedule 4).take 28) (initialLogical X)) := by
    rw [logicalRun, ← List.take_length (l := schedule 4), schedule_length,
      foldl_take_succ _ _ _ .exchange 28 (by rw [schedule_length]; omega)]
    rw [show (schedule 4).getD 28 .exchange = .exchange from exchange_entry]
    rfl
  rw [hrun]
  simp only [Piece.run]
  rw [hinv (otherSide ρ)]
  have hL := congrFun (logicalRun_schedule (initialLogical X)) ρ
  rw [hlog] at hL
  simp only [logicalStep] at hL
  rw [hL, initialLogical, ← along_mul, final_frame]

end IntegerMultBounds.MathlibTM2.M6.BitNode
