module

public import IntegerMultBounds.MathlibTM2.Node.Translate

/-! **The exact instructions of the node.** A translation or slot XOR acts on one wire with the
parameters of the child level: `framed p` saves `rows` and `L`, divided by the number of roles and
of slots, runs `p` and restores them (`framed_spec`). The slot phase runs at the node's own level
(`phaseInstr_monoSpecL`). With `FactorSpecL`, these are the programs of the node body on empty left
stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section

/-- Evaluate register updates at register names. -/
local macro "fupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj, reduceCtorEq,
  ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.wire.injEq, LReg.wtmp.injEq, LReg.bc.injEq,
  LReg.ph.injEq, LReg.lf.injEq, Fin.reduceEq, Fin.isValue, movedR, List.map_id, id]) <;> try rfl)

section Mono

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- **Exact instruction programs on empty left stacks.** -/
def MonoSpecL (prog : Pr P (nT BReg) Q A U)
    (bcRest : BReg → List (Fin (A + 4)) → Prop) (j u K ρ a₀ L rows n r w : ℕ) {R k : ℕ}
    (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n) (Tc : ℕ) (ins : Instr)
    (cm : ℕ) : Prop :=
  ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    (∀ y, S.L y = []) → NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
    (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ cm ∧ Exec body prog (mk v S) c (mk v' { S with R := R' }) ∧
      (∀ x, R' (reg (.wire x)) = encZ A w (execM e child Tc ins B x)) ∧
      ∀ i, (∀ x, i ≠ reg (.wire x)) → R' i = S.R i

lemma MonoSpecL.mono {prog : Pr P (nT BReg) Q A U}
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {j u K ρ a₀ L rows n r w : ℕ} {R k : ℕ}
    {e : Fin (m * k) → Fin n} {child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n}
    {Tc : ℕ} {ins : Instr} {cm cm' : ℕ}
    (h : MonoSpecL body prog bcRest j u K ρ a₀ L rows n r w e child Tc ins cm)
    (hc : cm ≤ cm') : MonoSpecL body prog bcRest j u K ρ a₀ L rows n r w e child Tc ins cm' :=
  fun B v S hL hN hB => by
    obtain ⟨v', c, R', hu, hc', he, hw, hfr⟩ := h B v S hL hN hB
    exact ⟨v', c, R', hu, hc'.trans hc, he, hw, hfr⟩

/-- The largest value of `f` over the instructions of `program ds`. -/
noncomputable def monoMax (ds : ComplexFramedExecution.Directions) (f : Instr → ℕ) : ℕ :=
  ((program ds).map f).foldr max 0

omit [Fintype BReg] in
lemma le_monoMax (ds : ComplexFramedExecution.Directions) (f : Instr → ℕ) {i : Instr}
    (h : i ∈ program ds) : f i ≤ monoMax ds f := by
  unfold monoMax
  generalize program ds = l at h ⊢
  induction l with
  | nil => simp at h
  | cons i' l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · simp only [List.map_cons, List.foldr_cons]
        exact le_max_of_le_right (ih h)

/-- Run `p` with `rows` and `L` divided by the numbers of roles and of slots. -/
def framed (p : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (saveDiv NW .rows) (.seq (saveDiv m .L) (.seq p (.seq (restoreMul m .L) (restoreMul NW .rows))))

/-- The step bound of `framed p` at level `j + 1`, with `p` within `cp` steps. -/
def framedCost (j u K R₀ cp : ℕ) : ℕ :=
  (8 * (NW * rowsAt R₀ j) + 8) + (8 * (K * bits u (j + 1)) + 8) + cp +
    (6 * (K * bits u j) + 6 * (K * bits u (j + 1)) + 13) +
    (6 * rowsAt R₀ j + 6 * (NW * rowsAt R₀ j) + 13)

/-- **Framed wire programs.** If `p`, with the parameters of the child level, turns the stream of
`Z` on wire `fw` into the stream of `T Z` and leaves every other register alone, then `framed p`
implements every instruction acting as `T` on wire `fw`. -/
theorem framed_spec {bcRest : BReg → List (Fin (A + 4)) → Prop} (p : Pr P (nT BReg) Q A U)
    (fw : NWire) {j u K ρ a₀ R₀ n r w Tc k : ℕ} (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (ins : Instr) (T : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (cp : ℕ) (hins : ∀ B, execM e child Tc ins B = Function.update B fw (T (B fw)))
    (hp : ∀ (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n),
      (∀ y, S.L y = []) → ParState S.R (j + 1) u K ρ a₀ (K * bits u j) (rowsAt R₀ j) n w (r * w) →
      RestBut bcRest n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) S.R →
      S.R (reg (.wire fw)) = encZ A w Z →
      ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ cp ∧
        Exec body p (mk v S) c
          (mk v' { S with R := Function.update S.R (reg (.wire fw)) (encZ A w (T Z)) })) :
    MonoSpecL body (framed p) bcRest j u K ρ a₀ (K * bits u (j + 1)) (rowsAt R₀ (j + 1)) n r w e
      child Tc ins (framedCost j u K R₀ cp) := by
  intro B v S hL hN hB
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hN.rest (.sc i) (by simp)
  have hm1 : 1 ≤ m := by norm_num [m]
  set rows₀ := S.R (reg .rows) with hrows₀
  set L₀ := S.R (reg .L) with hL₀
  set park₀ := S.R (reg .park) with hpark₀
  have hrows₀l : rows₀.length = NW * rowsAt R₀ j := hN.par .rows
  have hL₀l : L₀.length = m * (K * bits u j) := by
    rw [hL₀, hN.par .L, show bits u (j + 1) = m * bits u j from rfl]; ring
  -- save `rows` and `L`
  obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := saveDiv_exec body one_le_NW (X := .rows) (by simp) (by simp)
    (by simp) v S (hs 0) (hs 1)
  set R₁ := Function.update (Function.update S.R (reg .park) (rows₀.reverse ++ park₀))
    (reg .rows) (List.replicate (rows₀.length / NW) tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := saveDiv_exec body hm1 (X := .L) (by simp) (by simp)
    (by simp) v₁ { S with R := R₁ } (by dsimp only; rw [hR₁]; fupd; exact hs 0)
    (by dsimp only; rw [hR₁]; fupd; exact hs 1)
  dsimp only at hc₂ he₂
  have h1L : R₁ (reg .L) = L₀ := by rw [hR₁]; fupd
  have h1p : R₁ (reg .park) = rows₀.reverse ++ park₀ := by rw [hR₁]; fupd
  rw [h1L, h1p] at he₂
  rw [h1L] at hc₂
  set R₂ := Function.update (Function.update R₁ (reg .park) (L₀.reverse ++
    (rows₀.reverse ++ park₀))) (reg .L) (List.replicate (L₀.length / m) tick) with hR₂
  have h2o : ∀ x : LReg BReg, x ≠ .park → x ≠ .L → x ≠ .rows → R₂ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3
    rw [hR₂, Function.update_of_ne (reg_ne h2), Function.update_of_ne (reg_ne h1), hR₁,
      Function.update_of_ne (reg_ne h3), Function.update_of_ne (reg_ne h1)]
  have h2L : R₂ (reg .L) = List.replicate (K * bits u j) tick := by
    rw [hR₂, Function.update_self, hL₀l, Nat.mul_div_cancel_left _ (by norm_num [m])]
  have h2r : R₂ (reg .rows) = List.replicate (rowsAt R₀ j) tick := by
    rw [hR₂]; fupd; rw [hR₁]; fupd
    rw [hrows₀l, Nat.mul_div_cancel_left _ (Nat.pos_of_neZero NW)]
  have h2p : R₂ (reg .park) = L₀.reverse ++ (rows₀.reverse ++ park₀) := by rw [hR₂]; fupd
  -- the wire program
  have hpar₂ : ParState R₂ (j + 1) u K ρ a₀ (K * bits u j) (rowsAt R₀ j) n w (r * w) := by
    intro x
    by_cases hxL : x = .L
    · subst hxL; show (R₂ (reg .L)).length = _; rw [h2L, List.length_replicate]
    by_cases hxr : x = .rows
    · subst hxr; show (R₂ (reg .rows)).length = _; rw [h2r, List.length_replicate]
    by_cases hxp : x = .park
    · subst hxp; exact trivial
    have h := hN.par x
    rw [← h2o x hxp hxL hxr] at h
    cases x <;> first | exact trivial | exact absurd rfl hxL | exact absurd rfl hxr | exact h
  have hrest₂ : RestBut bcRest n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) R₂ := by
    intro x hx
    by_cases hxL : x = .L
    · subst hxL; exact trivial
    by_cases hxr : x = .rows
    · subst hxr; exact trivial
    by_cases hxp : x = .park
    · subst hxp; exact trivial
    rw [h2o x hxp hxL hxr]
    exact hN.rest x hx
  obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := hp v₂ { S with R := R₂ } (B fw) hL hpar₂ hrest₂
    (by dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hB fw)
  set R₃ := Function.update R₂ (reg (.wire fw)) (encZ A w (T (B fw))) with hR₃
  -- restore `L` and `rows`
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := restoreMul_exec body (c := m) (X := .L) (by simp) (by simp)
    (by simp) L₀.reverse (rows₀.reverse ++ park₀) v₃ { S with R := R₃ }
    (by dsimp only
        rw [hR₃, Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hN.rest .lenctr (by simp))
    (by dsimp only
        rw [hR₃, Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₃, Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
          List.length_reverse, hL₀l])
    (by dsimp only; rw [hR₃, Function.update_of_ne (reg_ne (by simp)), h2p])
  dsimp only at he₄ hc₄
  set R₄ := Function.update (Function.update R₃ (reg .park) (rows₀.reverse ++ park₀)) (reg .L)
    L₀.reverse.reverse with hR₄
  obtain ⟨v₅, c₅, hu₅, hc₅, he₅⟩ := restoreMul_exec body (c := NW) (X := .rows) (by simp)
    (by simp) (by simp) rows₀.reverse park₀ v₄ { S with R := R₄ }
    (by dsimp only
        rw [hR₄]
        fupd
        rw [hR₃]
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hN.rest .lenctr (by simp))
    (by dsimp only
        rw [hR₄]
        fupd
        rw [hR₃]
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₄]; fupd; rw [hR₃]; fupd; rw [h2r, List.length_replicate,
          List.length_reverse, hrows₀l])
    (by dsimp only; rw [hR₄]; fupd)
  dsimp only at he₅ hc₅
  set R₅ := Function.update (Function.update R₄ (reg .park) park₀) (reg .rows)
    rows₀.reverse.reverse with hR₅
  have hR₅' : R₅ = Function.update S.R (reg (.wire fw)) (encZ A w (T (B fw))) := by
    funext q
    by_cases h1 : q = reg .rows
    · subst h1; rw [hR₅]; fupd; rw [List.reverse_reverse]
    by_cases h2 : q = reg .park
    · subst h2; rw [hR₅]; fupd
    by_cases h3 : q = reg .L
    · subst h3; rw [hR₅]; fupd; rw [hR₄]; fupd; rw [List.reverse_reverse]
    rw [hR₅, Function.update_of_ne h1, Function.update_of_ne h2, hR₄, Function.update_of_ne h3,
      Function.update_of_ne h2, hR₃, Function.update_apply, Function.update_apply]
    split_ifs with h4
    · rfl
    · obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective q
      exact h2o x (fun h => h2 (by rw [h]; rfl)) (fun h => h3 (by rw [h]; rfl))
        (fun h => h1 (by rw [h]; rfl))
  have he := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))
  refine ⟨v₅, c₁ + (c₂ + (c₃ + (c₄ + c₅))), R₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_, he, ?_, ?_⟩
  · rw [hrows₀l] at hc₁
    rw [hR₃, Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
      List.length_reverse, hL₀l] at hc₄
    rw [hR₄] at hc₅
    simp only [Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte, hR₃] at hc₅
    rw [h2r, List.length_replicate, List.length_reverse, hrows₀l] at hc₅
    rw [hL₀l] at hc₂
    have hb : bits u (j + 1) = m * bits u j := rfl
    unfold framedCost
    rw [hb] at ⊢
    have : m * (K * bits u j) = K * (m * bits u j) := by ring
    omega
  · intro x
    rw [hR₅', hins]
    by_cases hx : x = fw
    · subst hx; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (reg_ne (by simp [hx])), Function.update_of_ne hx, hB x]
  · intro i hi
    rw [hR₅', Function.update_of_ne (hi fw)]

/-- **The slot phase instruction on empty left stacks.** -/
theorem phaseInstr_monoSpecL (hA : 5 ≤ A) {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {j u K ρ a₀ L R₀ n r w Tc : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K)
    (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (x : NWire) (i : Fin m) (cc : ZMod 4) :
    MonoSpecL body (phaseInstr x i cc) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
      (actMap a₀ ρ K (bits u (j + 1)) n hfit) child Tc (.phase x i cc)
      (phaseInstrCost u j a₀ ρ K (rowsAt R₀ j) n r w) := by
  intro B v S _ hN hB
  obtain ⟨v', c, hu, hc, he⟩ := phaseInstr_exec body hA hr hw hK hfit x i cc (B x) v S hN.par
    hN.rest (hB x)
  refine ⟨v', c, _, hu, hc, he, fun y => ?_, fun q hq => Function.update_of_ne (hq x) _ _⟩
  by_cases hy : y = x
  · subst hy; rw [Function.update_self]; simp only [execM, Function.update_self]; rfl
  · rw [Function.update_of_ne (reg_ne (by simp [hy])), hB y]
    simp only [execM, Function.update_of_ne hy]

/-- A slot XOR is the change of basis along `e_i + e_j` at the pivot `i`. -/
lemma basisMap_xor {i j : Fin m} (hij : i ≠ j) :
    basisMap (Pi.single i 1 + Pi.single j 1) i = ⇑(Networks.Certificates.T16.Impl.xorMap i j) := by
  funext a
  funext t
  rw [Networks.Certificates.T16.Impl.xorMap_apply]
  simp only [basisMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ht : t = j
  · subst ht; simp [hij, Ne.symm hij]
  · by_cases hti : t = i
    · subst hti; simp [hij, CharTwo.add_self_eq_zero]
    · simp [ht, hti]

lemma xor_pivot {i j : Fin m} (hij : i ≠ j) : (Pi.single i 1 + Pi.single j 1 : BinaryWalsh.Address m) i = 1 := by
  simp [Ne.symm hij]

end Mono

end

end IntegerMultBounds.MathlibTM2.LayerMachine
