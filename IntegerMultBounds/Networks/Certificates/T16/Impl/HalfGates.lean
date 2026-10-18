module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Machine

/-! **Half-integral gates.** The layer machine runs a gate `x_t ← x_t + Σ c x_s` exactly when
every `2 c` is an integer. A single-term gate with a dyadic coefficient `c = n / 2^k` becomes
`k - 1` halvings of its source, one half-integral gate and `k - 1` doublings of the source; a
dyadic scaling of one wire becomes `k - 1` halvings and one half-integral scaling. Every rewrite is
exact (`moduleRun_fitGate`), so machine programs keep their action and their child calls. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open FramedCircuit BinaryWalsh

variable {ι : Type} [DecidableEq ι]
variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Halve wire `s`. -/
def halveGate (s : ι) : Circuit.Gate ι ℚ := ⟨s, [(s, -1 / 2)]⟩

/-- Double wire `s`. -/
def doubleGate (s : ι) : Circuit.Gate ι ℚ := ⟨s, [(s, 1)]⟩

theorem moduleGate_halve (s : ι) (x : ι → E) :
    moduleGate (halveGate s) x = Function.update x s ((1 / 2 : ℚ) • x s) := by
  simp only [moduleGate, halveGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  congr 1
  rw [← one_smul ℚ (x s), smul_smul, ← add_smul]
  norm_num

theorem moduleGate_double (s : ι) (x : ι → E) :
    moduleGate (doubleGate s) x = Function.update x s ((2 : ℚ) • x s) := by
  simp only [moduleGate, doubleGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, one_smul]
  congr 1
  rw [two_smul]

theorem moduleRun_halves (s : ι) (j : ℕ) (x : ι → E) :
    moduleRun (List.replicate j (halveGate s)) x =
      Function.update x s (((1 / 2 : ℚ) ^ j) • x s) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, moduleRun_cons, moduleGate_halve, ih, Function.update_self,
      Function.update_idem, smul_smul, pow_succ]

theorem moduleRun_doubles (s : ι) (j : ℕ) (x : ι → E) :
    moduleRun (List.replicate j (doubleGate s)) x = Function.update x s (((2 : ℚ) ^ j) • x s) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, moduleRun_cons, moduleGate_double, ih, Function.update_self,
      Function.update_idem, smul_smul, pow_succ]

/-- The machine gates of a gate. -/
def fitGate (g : Circuit.Gate ι ℚ) : List (Circuit.Gate ι ℚ) :=
  match g.terms with
  | [(s, c)] =>
    if s = g.target then
      List.replicate (Nat.log 2 c.den - 1) (halveGate s) ++
        [⟨s, [(s, (1 + c) * 2 ^ (Nat.log 2 c.den - 1) - 1)]⟩]
    else
      List.replicate (Nat.log 2 c.den - 1) (halveGate s) ++
        [⟨g.target, [(s, c * 2 ^ (Nat.log 2 c.den - 1))]⟩] ++
          List.replicate (Nat.log 2 c.den - 1) (doubleGate s)
  | _ => [g]

theorem moduleRun_append' (gs hs : List (Circuit.Gate ι ℚ)) (x : ι → E) :
    moduleRun (gs ++ hs) x = moduleRun hs (moduleRun gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- **Fitting is exact.** -/
theorem moduleRun_fitGate (g : Circuit.Gate ι ℚ) (x : ι → E) :
    moduleRun (fitGate g) x = moduleGate g x := by
  obtain ⟨t, terms⟩ := g
  unfold fitGate
  match terms with
  | [(s, c)] =>
    simp only
    set j := Nat.log 2 c.den - 1
    have hj : (2 : ℚ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
    split_ifs with hst
    · subst hst
      rw [moduleRun_append', moduleRun_halves, moduleRun_cons, moduleRun_nil]
      simp only [moduleGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Function.update_self, Function.update_idem]
      congr 1
      rw [smul_smul, ← add_smul, ← one_smul ℚ (x s), smul_smul, smul_smul, ← add_smul]
      have h : (((1 / 2 : ℚ) ^ j + ((1 + c) * 2 ^ j - 1) * (1 / 2) ^ j) * 1) = 1 + c * 1 := by
        linear_combination (1 + c) * hj
      rw [h]
    · rw [moduleRun_append', moduleRun_append', moduleRun_halves, moduleRun_cons, moduleRun_nil,
        moduleRun_doubles]
      simp only [moduleGate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [Function.update_of_ne (Ne.symm hst), Function.update_self,
        Function.update_of_ne hst, Function.update_self, Function.update_comm hst]
      have e1 : c * 2 ^ j * (1 / 2 : ℚ) ^ j = c := by rw [mul_assoc, hj, mul_one]
      have e2 : (2 : ℚ) ^ j • (1 / 2 : ℚ) ^ j • x s = x s := by rw [smul_smul, hj, one_smul]
      rw [Function.update_idem, smul_smul, e1, e2]
      exact Function.update_eq_self_iff.mpr (Function.update_of_ne hst _ _).symm
  | [] => simp [moduleRun]
  | _ :: _ :: _ => simp [moduleRun]

/-! ### Half-integral coefficients -/

/-- Every coefficient of the gate is half an integer. -/
def HalfGate (g : Circuit.Gate ι ℚ) : Prop := ∀ p ∈ g.terms, (2 * p.2).den = 1

/-- Dyadic coefficients, and half-integral ones unless the gate has a single term. -/
def DyadicGate (g : Circuit.Gate ι ℚ) : Prop :=
  (∀ p ∈ g.terms, ∃ k, p.2.den = 2 ^ k) ∧ (g.terms.length = 1 ∨ HalfGate g)

theorem den_eq_one_of_eq_int {q : ℚ} {z : ℤ} (h : q = z) : q.den = 1 := by
  rw [h]; exact Rat.den_intCast z

theorem two_mul_pow_dyadic {c : ℚ} {k : ℕ} (hk : c.den = 2 ^ k) :
    ∃ z : ℤ, 2 * (c * 2 ^ (k - 1)) = z := by
  have hc : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
  rw [hk] at hc
  push_cast at hc
  cases k with
  | zero =>
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℤ, c = z₀ := ⟨c.num, by simpa using hc⟩
    exact ⟨2 * z₀, by rw [hz₀]; push_cast; ring⟩
  | succ k =>
    refine ⟨c.num, ?_⟩
    rw [← hc, Nat.add_sub_cancel, pow_succ]
    ring

theorem fitGate_half (g : Circuit.Gate ι ℚ) (hg : DyadicGate g) : ∀ g' ∈ fitGate g, HalfGate g' := by
  obtain ⟨t, terms⟩ := g
  obtain ⟨hden, hlen⟩ := hg
  have hhalve : ∀ s : ι, HalfGate (halveGate s) := fun s p hp => by
    simp only [halveGate, List.mem_singleton] at hp; subst hp; norm_num
  have hdouble : ∀ s : ι, HalfGate (doubleGate s) := fun s p hp => by
    simp only [doubleGate, List.mem_singleton] at hp; subst hp; norm_num
  unfold fitGate
  match terms, hden, hlen with
  | [(s, c)], hden, _ =>
    obtain ⟨k, hk⟩ := hden (s, c) List.mem_cons_self
    have hlog : Nat.log 2 c.den = k := by rw [hk, Nat.log_pow (by norm_num)]
    simp only [hlog]
    obtain ⟨z, hz⟩ := two_mul_pow_dyadic hk
    intro g' hg'
    split_ifs at hg' with hst
    · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hg'
      rcases hg' with ⟨-, rfl⟩ | rfl
      · exact hhalve s
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        cases k with
        | zero =>
          refine den_eq_one_of_eq_int (z := z) ?_
          simp only [Nat.zero_sub, pow_zero, mul_one] at hz ⊢
          linear_combination hz
        | succ k =>
          refine den_eq_one_of_eq_int (z := 2 ^ (k + 1) + z - 2) ?_
          simp only [Nat.add_sub_cancel] at hz ⊢
          push_cast
          linear_combination (2 : ℚ) ^ k * 2 * 1 + hz - 2 ^ k * 2
    · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hg'
      rcases hg' with (⟨-, rfl⟩ | rfl) | ⟨-, rfl⟩
      · exact hhalve s
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact den_eq_one_of_eq_int hz
      · exact hdouble s
  | [], _, _ => intro g' hg'; simp only [List.mem_singleton] at hg'; subst hg'; intro p hp; simp at hp
  | a :: b :: rest, _, hlen =>
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst hg'
    rcases hlen with h | h
    · simp at h
    · exact h

/-! ### Fitted machine programs -/

/-- The machine instructions of an instruction, with fitted gates. -/
def fitInstr : MInstr ι → List (MInstr ι)
  | .gate g => (fitGate g).map MInstr.gate
  | i => [i]

/-- The fitted machine program. -/
def fitProgram (prog : List (MInstr ι)) : List (MInstr ι) := prog.flatMap fitInstr

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

theorem runM_gates (gs : List (Circuit.Gate ι ℚ)) (x : ι → S) :
    runM ρ (gs.map MInstr.gate) x = moduleRun gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- **Fitting keeps the action and the child calls.** -/
theorem fitProgram_spec (prog : List (MInstr ι)) :
    (∀ y : ι → S, runM ρ (fitProgram prog) y = runM ρ prog y) ∧
      mprogramChildren (fitProgram prog) = mprogramChildren prog := by
  induction prog with
  | nil => exact ⟨fun _ => rfl, rfl⟩
  | cons i prog ih =>
    refine ⟨fun y => ?_, ?_⟩
    · rw [fitProgram, List.flatMap_cons, ← fitProgram, runM_append, ih.1]
      cases i with
      | gate g =>
        change runM ρ prog (runM ρ ((fitGate g).map MInstr.gate) y) = runM ρ prog (moduleGate g y)
        rw [runM_gates, moduleRun_fitGate]
      | prim w p => rfl
    · rw [fitProgram, List.flatMap_cons, ← fitProgram, mprogramChildren_append, ih.2,
        show mprogramChildren (i :: prog) = mprogramChildren [i] + mprogramChildren prog from
          mprogramChildren_append [i] prog]
      cases i with
      | gate g =>
        congr 1
        simp [fitInstr, mprogramChildren, List.filter_map, MInstr.isChild, Function.comp_def]
      | prim w p => rfl

/-- Every gate of a machine program. -/
def MInstr.gateOf : MInstr ι → Option (Circuit.Gate ι ℚ)
  | .gate g => some g
  | _ => none

theorem fitProgram_half (prog : List (MInstr ι))
    (h : ∀ g, MInstr.gate g ∈ prog → DyadicGate g) :
    ∀ g, MInstr.gate g ∈ fitProgram prog → HalfGate g := by
  intro g hg
  rw [fitProgram, List.mem_flatMap] at hg
  obtain ⟨i, hi, hg⟩ := hg
  cases i with
  | gate g₀ =>
    simp only [fitInstr, List.mem_map, MInstr.gate.injEq] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact fitGate_half g₀ (h g₀ hi) g' hg'
  | prim w p => simp [fitInstr] at hg

end IntegerMultBounds.Networks.Certificates.T16.Impl
