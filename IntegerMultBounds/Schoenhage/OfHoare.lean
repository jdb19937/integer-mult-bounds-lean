module

public import IntegerMultBounds.Schoenhage.PrimLift
public import IntegerMultBounds.Schoenhage.Ops

/-! Programs halt in a unique configuration (`run_halt_unique`, `HoareTime.det`),
and a bank of word tapes is determined by its physical tapes and heads
(`enc_injective`). So any program with an exact contract between word banks is
a word-program primitive whose semantics is that contract and whose cost is its
least bound (`Prim.ofHoare`, `runs_ofHoare`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {t q a : ℕ}

/-! ### Determinism -/

theorem run_halt_unique (M : Program t q a) : ∀ (k k' : ℕ) (c c₁ c₂ : Config t q a),
    run M k c = some c₁ → step M c₁ = none → run M k' c = some c₂ → step M c₂ = none → c₁ = c₂
  | 0, 0, c, c₁, c₂, h1, _, h2, _ => by simp [run] at h1 h2; rw [← h1, ← h2]
  | 0, k' + 1, c, c₁, c₂, h1, s1, h2, _ => by
    simp only [run, Option.some.injEq] at h1
    subst h1
    simp [run, s1] at h2
  | k + 1, 0, c, c₁, c₂, h1, _, h2, s2 => by
    simp only [run, Option.some.injEq] at h2
    subst h2
    simp [run, s2] at h1
  | k + 1, k' + 1, c, c₁, c₂, h1, s1, h2, s2 => by
    simp only [run] at h1 h2
    cases hs : step M c with
    | none => simp [hs] at h1
    | some d =>
      rw [hs] at h1 h2
      exact run_halt_unique M k k' d c₁ c₂ h1 s1 h2 s2

theorem HoareTime.det {M : Program t q a} {v u₁ u₂ : Tapes t a} {k₁ k₂ : ℕ}
    (h₁ : HoareTime M (· = v) (· = u₁) k₁) (h₂ : HoareTime M (· = v) (· = u₂) k₂) : u₁ = u₂ := by
  obtain ⟨n₁, c₁, -, r₁, s₁, p₁⟩ := h₁ v rfl
  obtain ⟨n₂, c₂, -, r₂, s₂, p₂⟩ := h₂ v rfl
  rw [← p₁, ← p₂, run_halt_unique M n₁ n₂ _ c₁ c₂ r₁ s₁ r₂ s₂]

/-! ### Word tapes from their cells -/

theorem syms_injective : Function.Injective syms := fun ws vs h => by
  rw [← parse_syms ws, ← parse_syms vs, h]

theorem wordTape_injective {l l' : List (Fin (a + 4))} (hl : ∀ x ∈ l, x ≠ blank) (hl' : ∀ x ∈ l', x ≠ blank)
    (h : wordTape l = wordTape l') : l = l' := by
  apply List.ext_getElem?
  intro n
  have hn := congrFun h (n : ℤ)
  simp only [wordTape, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast] at hn
  cases e : l[n]? with
  | none =>
    cases e' : l'[n]? with
    | none => rfl
    | some y =>
      rw [e, e'] at hn
      exact absurd hn.symm (hl' y (List.mem_of_getElem? e'))
  | some x =>
    cases e' : l'[n]? with
    | none =>
      rw [e, e'] at hn
      exact absurd hn (hl x (List.mem_of_getElem? e))
    | some y => rw [e, e'] at hn; simp at hn; rw [hn]

theorem cells_ne_blank (ws : List (List Bool)) : ∀ x ∈ cells (a := a) ws, x ≠ blank := by
  intro x hx
  simp only [cells, List.mem_map] at hx
  obtain ⟨o, -, rfl⟩ := hx
  exact sym_ne_blank o

theorem words_of_tape {T T' : WTape} (h : T.tape (a := a) = T'.tape) : T.words = T'.words := by
  have hc := wordTape_injective (cells_ne_blank _) (cells_ne_blank _) h
  exact syms_injective ((List.map_injective_iff.mpr sym_injective) hc)

theorem split_clen : ∀ (A B A' B' : List (List Bool)), A ++ B = A' ++ B' → clen A = clen A' → A = A'
  | [], _, [], _, _, _ => rfl
  | [], _, a' :: A', _, _, hc => by simp at hc <;> omega
  | a :: A, _, [], _, _, hc => by simp at hc <;> omega
  | a :: A, B, a' :: A', B', h, hc => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [clen_cons] at hc
    rw [split_clen A B A' B' h (by omega)]

theorem WTape.ext_tape {T T' : WTape} (ht : T.tape (a := a) = T'.tape) (hp : T.pos = T'.pos) : T = T' := by
  have hw := words_of_tape ht
  have hc : clen T.left = clen T'.left := by simpa [WTape.pos] using hp
  simp only [WTape.words] at hw
  have hl := split_clen _ _ _ _ hw (by rw [clen_reverse, clen_reverse, hc])
  have hr : T.right = T'.right := by rw [hl] at hw; exact List.append_cancel_left hw
  rw [List.reverse_inj] at hl
  cases T; cases T'; simp_all

theorem enc_injective : Function.Injective (enc (t := t) (a := a)) := by
  intro σ σ' h
  funext x
  have hh := congrFun (congrArg Tapes.head h) x
  have ht := congrFun (congrArg Tapes.tape h) x
  exact WTape.ext_tape ht hh

/-! ### Primitives from contracts -/

/-- `M` turns the bank `σ` into `σ'` within `k` steps. -/
def HoareTo (M : Program t q a) (σ σ' : Fin t → WTape) (k : ℕ) : Prop :=
  HoareTime M (· = enc σ) (· = enc σ') k

open Classical in
/-- The primitive of any program, with its exact contract as semantics and its least bound as cost. -/
noncomputable def Prim.ofHoare (M : Program t q a) (ht : 0 < t) : Prim a :=
  Prim.ofProgram M ht (fun σ => ∃ k σ', HoareTo M σ σ' k)
    (fun σ => if h : ∃ k σ', HoareTo M σ σ' k then (Nat.find_spec h).choose else σ)
    (fun σ => if h : ∃ k σ', HoareTo M σ σ' k then Nat.find h else 0)
    (fun σ h => by
      simp only [h, ↓reduceDIte]
      exact (Nat.find_spec h).choose_spec)

theorem ofHoare_spec (M : Program t q a) (ht : 0 < t) {σ σ' : Fin t → WTape} {k : ℕ}
    (h : HoareTo M σ σ' k) :
    (Prim.ofHoare M ht).pre σ ∧ (Prim.ofHoare M ht).sem σ = σ' ∧ (Prim.ofHoare M ht).cost σ ≤ k := by
  classical
  have hpre : ∃ k σ', HoareTo M σ σ' k := ⟨k, σ', h⟩
  refine ⟨hpre, ?_, ?_⟩
  · change (if h : ∃ k σ', HoareTo M σ σ' k then (Nat.find_spec h).choose else σ) = σ'
    simp only [hpre, ↓reduceDIte]
    exact enc_injective (HoareTime.det (Nat.find_spec hpre).choose_spec h)
  · change (if h : ∃ k σ', HoareTo M σ σ' k then Nat.find h else 0) ≤ k
    simp only [hpre, ↓reduceDIte]
    exact Nat.find_min' hpre ⟨σ', h⟩

/-- Calling the primitive of a contract on slotted tapes. -/
theorem runs_ofHoare (M : Program t q a) (ht : 0 < t) {s : ℕ} {slot : Fin t → Fin s}
    (hinj : Function.Injective slot) {σ : Fin s → WTape} {τ' : Fin t → WTape} {k : ℕ}
    (h : HoareTo M (σ ∘ slot) τ' k) :
    Runs (.prim (Prim.ofHoare M ht) slot hinj) σ (· = upd σ slot τ') k := by
  obtain ⟨hpre, hsem, hcost⟩ := ofHoare_spec M ht h
  exact ⟨_, _, Exec.prim hpre, congrArg (upd σ slot) hsem, hcost⟩

/-- The same over a larger alphabet. -/
theorem runs_ofHoare_lift (M : Program t q 0) (ht : 0 < t) {s : ℕ} {slot : Fin t → Fin s}
    (hinj : Function.Injective slot) {σ : Fin s → WTape} {τ' : Fin t → WTape} {k : ℕ}
    (h : HoareTo M (σ ∘ slot) τ' k) :
    Runs (a := a) (.prim (Prim.lift (Prim.ofHoare M ht)) slot hinj) σ (· = upd σ slot τ') k := by
  obtain ⟨hpre, hsem, hcost⟩ := ofHoare_spec M ht h
  exact ⟨_, _, Exec.prim (P := Prim.lift (Prim.ofHoare M ht)) hpre, congrArg (upd σ slot) hsem, hcost⟩

end IntegerMultBounds.Schoenhage
