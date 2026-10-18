module

public import IntegerMultBounds.MathlibTM2.Node.Regs
public import IntegerMultBounds.MathlibTM2.Node.Gate
public import IntegerMultBounds.MathlibTM2.Layer.LayerZ
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# The node body of the layer machine

`nodeBody ds fp mp` runs the scaled node `nodeM` of `Layer/NodeZ.lean` at level `j + 1` on the
array register `io`, with the factor instructions of `program ds` supplied as programs
`fp fw g` and the exact instructions (translations, slot XORs, slot phases) as programs `mp ins`.
With `R = rowsAt R₀ j` rows per wire and the active bits `e i = a₀ + ρ + K i` (`actMap`), its
stages are:

1. `splitProg`: `routeBlocks` sends row `NW g + i` of `io` (rows of `2^n r w` symbols, counted by
   `rowctr`) onto the temporary of the data wire `inl (wireOf i)`, and `moveR` puts every
   temporary in forward order on its wire; the data wires hold the bank `bankZ (toBank R Z)`
   (`blocksTo_roles_syms`).
2. `zeroCentres`: the eight private centres `inr c` receive the zero stream of the shape of wire
   `inl 0`.
3. `tcBuild ds`: `Tc := expZ u ds j` (`expProg` with the gate and factor counts of `program ds`,
   `expZ_eq_expSeq`).
4. `(program ds).map (instrProg fp mp)`: `gateProg` on the bank for a gate, `fp fw g` for a
   factor and `mp ins` for an exact instruction (`instrs_exec`, an induction over the instruction
   list). A slot phase is `phaseInstr` (`slotPass`: a strided mask and `phaseProg`).
5. `uclear Tc`.
6. `clearCentres`: the centres are emptied.
7. `mergeProg`: `mergeBlocks` merges the data wires by row role onto `racc` (the row count on
   `rows`), and `moveR` puts the result in forward order on `io`.

**Main theorem** (`nodeBody_exec`, `nodeBody_exec_layerZ`). From `ParState` at level `j + 1`
(`rows = rowsAt R₀ (j + 1)`, `rw = r w`), `Rest` and `io` holding `encZ A w Z`, and with every
factor instruction of `program ds` implemented by `fp` in the sense of `FactorSpec` (child
semantics `layerZ u ds R₀ j` on the slots, child exponent `expZ u ds j`) and every exact
instruction by `mp` in the sense of `MonoSpec`, the node body ends with `io` holding
`encZ A w (layerZ u ds R₀ (j + 1) e Z)`, every other register and `user` as before, within
`nodeCost ds u j K ρ a₀ R n r w cf cm` steps. Between two instructions the registers satisfy
`NodeRegs` (`Node/Regs.lean`).

**Cost.** `nodeCost` is the sum of the stage bounds: split and merge `O(V + NW R)` with
`V = NW R 2^n r w`; the centres `O(R 2^n r w)`; the exponent program (`expCost`); `G` gates
(`gateCost`), `F` factors (`cf` each) and `Mo` exact instructions (`cm` each), `G`, `F`, `Mo` the
gate, factor and exact-instruction counts of `program ds`; clearing `Tc`.

**Register use.** `sc 0` holds `a₀ + ρ` (slot phases); `sc 1` holds `k`; `sc 2`, `sc 3`, `sc 4`
are spares; `sc 5` parks the top of `lev` and is a spare of `strideMask`. The scan slot `st` holds
automaton states, `cs` the row counter of the routing.

**Devices.** `withPred` (run a program with `lev` one shorter), `exec_upd` (an execution ending in
one register update, with an opaque register file), `resid4` and `disp4` (a residue modulo `4` in
a scan slot and the dispatch on it), and `seqList_passes` (a list of passes on pairwise disjoint
register sets).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg


/-! ### Instruction counts -/

/-- The number of gates of an instruction list. -/
def gateCount : List Instr → ℕ
  | [] => 0
  | .gate _ :: l => gateCount l + 1
  | .factor _ _ :: l => gateCount l
  | .trans _ _ :: l => gateCount l
  | .xor _ _ _ :: l => gateCount l
  | .phase _ _ _ :: l => gateCount l

/-- The number of factors of an instruction list. -/
def factorCount : List Instr → ℕ
  | [] => 0
  | .gate _ :: l => factorCount l
  | .factor _ _ :: l => factorCount l + 1
  | .trans _ _ :: l => factorCount l
  | .xor _ _ _ :: l => factorCount l
  | .phase _ _ _ :: l => factorCount l

/-- The number of translations, slot XORs and slot phases of an instruction list. -/
def monoCount : List Instr → ℕ
  | [] => 0
  | .gate _ :: l => monoCount l
  | .factor _ _ :: l => monoCount l
  | .trans _ _ :: l => monoCount l + 1
  | .xor _ _ _ :: l => monoCount l + 1
  | .phase _ _ _ :: l => monoCount l + 1

/-- The exponent of a scaled program: one per gate and `Tc` per factor. -/
lemma progExp_eq (Tc : ℕ) : ∀ l : List Instr, progExp Tc l = gateCount l + factorCount l * Tc
  | [] => by simp [progExp, gateCount, factorCount]
  | .gate _ :: l => by rw [progExp, gateCount, factorCount, progExp_eq Tc l]; ring
  | .factor _ _ :: l => by rw [progExp, gateCount, factorCount, progExp_eq Tc l]; ring
  | .trans _ _ :: l => by rw [progExp, gateCount, factorCount, progExp_eq Tc l]
  | .xor _ _ _ :: l => by rw [progExp, gateCount, factorCount, progExp_eq Tc l]
  | .phase _ _ _ :: l => by rw [progExp, gateCount, factorCount, progExp_eq Tc l]

/-- The child exponent is the exponent sequence of the gate and factor counts. -/
lemma expZ_eq_expSeq (u : ℕ) (ds : ComplexFramedExecution.Directions) (j : ℕ) :
    expZ u ds j = expSeq (gateCount (program ds)) (factorCount (program ds)) u j :=
  eq_expSeq (e := expZ u ds) rfl (fun i => by
    rw [expZ, nodeExp, progExp_eq, Nat.mul_comm]) j

/-- `bits u j = m ^ j u` is the exponent sequence with `G = 0`, `F = m`. -/
lemma bits_eq_expSeq (u : ℕ) (j : ℕ) : bits u j = expSeq 0 m u j :=
  eq_expSeq (e := bits u) rfl (fun i => by rw [bits, Nat.zero_add]) j

/-- `m ≡ 1` modulo `4`, so `bits u j ≡ u`. -/
lemma bits_mod_four (u : ℕ) : ∀ j, bits u j % 4 = u % 4
  | 0 => rfl
  | j + 1 => by
      rw [bits, Nat.mul_mod, bits_mod_four u j, show m % 4 = 1 by norm_num [m], one_mul,
        Nat.mod_mod]

/-- `i ^ (27 k)` only depends on `k` modulo `4`, through `3 (k mod 4)`. -/
lemma pow_I_27 (k : ℕ) :
    (⟨0, 1⟩ : GaussianInt) ^ (27 * k) = (⟨0, 1⟩ : GaussianInt) ^ ((3 * (k % 4)) % 4) := by
  have h4 : (⟨0, 1⟩ : GaussianInt) ^ 4 = 1 := by decide
  rw [pow_eq_pow_mod _ h4]
  congr 1
  omega

/-! ### Host utilities -/

section Utils

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- One `moveStep` from a nonempty register. -/
lemma moveStep_run {i j : Fin T} (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) {x : Fin (A + 4)}
    {rest : List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A) (hS : S.R i = x :: rest) :
    (moveStep i j f : Act T Q A U).run (mk v S) =
      mk { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (f x :: S.R j) } := by
  simp [moveStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
    Function.update_of_ne hij.symm]

/-- Run `p` with the top symbol of `lv` parked on the empty `t`. -/
def withPred (lv t : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (moveStep lv t id)) (.seq p (.act (moveStep t lv id)))

/-- `withPred`: if `p` runs from the state with `lv` popped onto `t` and leaves `lv` and `t`
alone, the top symbol returns to `lv` and `t` ends empty; the other registers end as `p` left
them. -/
lemma withPred_exec {lv t : Fin T} (hlt : lv ≠ t) {p : Pr P T Q A U} {x : Fin (A + 4)}
    {rest : List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A) (hlv : S.R lv = x :: rest)
    (ht : S.R t = []) {v₁ : HS T Q A U} {c : ℕ} {R' : Fin T → List (Fin (A + 4))}
    (hp : Exec body p (mk { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R lv rest) t [x] }) c
      (mk v₁ { S with R := R' }))
    (hlv' : R' lv = rest) (ht' : R' t = [x]) :
    ∃ (v₂ : HS T Q A U) (R'' : Fin T → List (Fin (A + 4))), v₂.user = v₁.user ∧
      Exec body (withPred lv t p) (mk v S) (c + 2) (mk v₂ { S with R := R'' }) ∧
      R'' lv = S.R lv ∧ R'' t = S.R t ∧ ∀ k, k ≠ lv → k ≠ t → R'' k = R' k := by
  have h1 := Exec.act (body := body) (moveStep lv t id) (mk v S)
  rw [moveStep_run hlt id v S hlv, ht] at h1
  have h2 := Exec.act (body := body) (moveStep t lv id) (mk v₁ { S with R := R' })
  rw [moveStep_run (Ne.symm hlt) id v₁ { S with R := R' } ht'] at h2
  refine ⟨{ v₁ with sym := some x, flag := ([] : List (Fin (A + 4))).head?.isSome },
    Function.update (Function.update R' t []) lv (x :: rest), rfl,
    Exec.cast (Exec.seq h1 (Exec.seq hp h2)) (by ring) (by simp only [id, hlv']), ?_, ?_, ?_⟩
  · rw [Function.update_self, hlv]
  · rw [Function.update_of_ne (Ne.symm hlt), Function.update_self, ht]
  · intro k hk1 hk2
    rw [Function.update_of_ne hk1, Function.update_of_ne hk2]

/-- An execution ending in an update of one register, with the register file made opaque. -/
lemma exec_upd {p : Pr P T Q A U} {v v' : HS T Q A U} {S : Stacks T A}
    {R : Fin T → List (Fin (A + 4))} {c : ℕ} {b : Fin T} {l : List (Fin (A + 4))}
    (h : Exec body p (mk v { S with R := R }) c (mk v' { S with R := Function.update R b l })) :
    ∃ R' : Fin T → List (Fin (A + 4)),
      Exec body p (mk v { S with R := R }) c (mk v' { S with R := R' }) ∧ R' b = l ∧
      ∀ k, k ≠ b → R' k = R k :=
  ⟨_, h, Function.update_self .., fun _ hk => Function.update_of_ne hk ..⟩

/-- One step of the residue count: move the top of `i` onto `j` and advance the counter in the
scan slot `cs` modulo `4`. -/
def cntStep (i j cs : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => v.sym.getD blank)
      (.load (fun v => { v with scan := Function.update v.scan cs (nextC 4 (v.scan cs)) })
        (peekR i)))

/-- The counting loop: `2 |l| + 1` steps; the symbols of `i` move onto `j` (reversed) and the
scan slot `cs` advances by `|l|` modulo `4`. -/
theorem cntStep_loop {i j : Fin T} (hij : i ≠ j) (cs : Fin T) :
    ∀ (l : List (Fin (A + 4))) (c : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome → (v.scan cs).val = c % 4 →
      ∃ v', v'.user = v.user ∧ (v'.scan cs).val = (c + l.length) % 4 ∧
        Exec body (.loop (·.flag) (.act (cntStep i j cs))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := movedR S.R i j id l }) := by
  intro l
  induction l with
  | nil =>
      intro c v S hS hf hc
      refine ⟨v, rfl, by simpa using hc, ?_⟩
      have : ({ S with R := movedR S.R i j id [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [movedR]
          · by_cases hk' : k = i
            · subst hk'; simp [movedR, hk, hS]
            · simp [movedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro c v S hS hf hc
      have hn := nextC_val (A := A) (W := 4) (n := c) (by norm_num) (by omega) hc
      obtain ⟨v', hu, hsc, he⟩ := ih (c + 1)
        { v with sym := some e, scan := Function.update v.scan cs (nextC 4 (v.scan cs)),
                 flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (e :: S.R j) }
        (by simp [Function.update_of_ne hij]) rfl (by simpa using hn)
      refine ⟨v', hu, by rw [hsc, List.length_cons]; ring_nf, ?_⟩
      have hrun : (cntStep i j cs : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, scan := Function.update v.scan cs (nextC 4 (v.scan cs)),
                      flag := rest.head?.isSome }
            { S with R := Function.update (Function.update S.R i rest) j (e :: S.R j) } := by
        simp [cntStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (cntStep i j cs) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [movedR]
      · by_cases hk' : k = i
        · subst hk'; simp [movedR, hk]
        · simp [movedR, hk, hk']

/-- The residue of `|i|` modulo `4` into the scan slot `cs`: count the symbols of `i` while moving
them onto the empty `t`, then move them back. -/
def resid4 (i t cs : Fin T) : Pr P T Q A U :=
  .seq (.act (initCounter cs i)) (.seq (.loop (·.flag) (.act (cntStep i t cs))) (moveR t i id))

/-- `resid4`: the registers end as they started, the scan slot `cs` holds `|i| mod 4`;
`4 |i| + 4` steps. -/
theorem resid4_exec {i t : Fin T} (hit : i ≠ t) (cs : Fin T) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R t = []) :
    ∃ v', v'.user = v.user ∧ (v'.scan cs).val = (S.R i).length % 4 ∧
      Exec body (resid4 i t cs) (mk v S) (4 * (S.R i).length + 4) (mk v' S) := by
  have he₀ := Exec.act (body := body) (initCounter cs i) (mk v S)
  have hrun : (initCounter cs i : Act T Q A U).run (mk v S) =
      mk { v with scan := Function.update v.scan cs 0, flag := (S.R i).head?.isSome } S := rfl
  rw [hrun] at he₀
  obtain ⟨v₁, hu₁, hsc₁, he₁⟩ := cntStep_loop body hit cs (S.R i) 0
    { v with scan := Function.update v.scan cs 0, flag := (S.R i).head?.isSome } S rfl rfl
    (by simp)
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body t i (Ne.symm hit) id v₁
    { S with R := movedR S.R i t id (S.R i) }
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂, hsc₁, Nat.zero_add],
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ he₂)) ?_ ?_⟩
  · simp [movedR, ht]; ring
  · congr 1
    cases S with
    | mk inp out L R =>
      simp only at ht ⊢
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [movedR, hit, ht]
      · by_cases hk' : k = t
        · subst hk'; simp [movedR, hk, ht]
        · simp [movedR, hk, hk']

/-- Run `p s` for the value `s < 4` of the scan slot `cs`. -/
def disp4 (cs : Fin T) (p : Fin 4 → Pr P T Q A U) : Pr P T Q A U :=
  .cond (fun v => decide ((v.scan cs).val = 0)) (p 0)
    (.cond (fun v => decide ((v.scan cs).val = 1)) (p 1)
      (.cond (fun v => decide ((v.scan cs).val = 2)) (p 2) (p 3)))

/-- `disp4` runs the branch of the value `q` of the scan slot, in at most three more steps. -/
lemma disp4_exec (cs : Fin T) (p : Fin 4 → Pr P T Q A U) (q : Fin 4) (v : HS T Q A U)
    (S : Stacks T A) (hq : (v.scan cs).val = q.val) {c : ℕ}
    {t : Store (HΓ (T := T) A) (HS T Q A U)} (h : Exec body (p q) (mk v S) c t) :
    ∃ c', c' ≤ c + 3 ∧ Exec body (disp4 cs p) (mk v S) c' t := by
  obtain ⟨q, hq4⟩ := q
  simp only at hq
  interval_cases q
  · exact ⟨c + 1, by omega, .cond_true (by simp [hq]) h⟩
  · exact ⟨c + 1 + 1, by omega, .cond_false (by simp [hq]) (.cond_true (by simp [hq]) h)⟩
  · exact ⟨c + 1 + 1 + 1, by omega, .cond_false (by simp [hq])
      (.cond_false (by simp [hq]) (.cond_true (by simp [hq]) h))⟩
  · exact ⟨c + 1 + 1 + 1, by omega, .cond_false (by simp [hq])
      (.cond_false (by simp [hq]) (.cond_false (by simp [hq]) h))⟩

/-- **A list of passes on disjoint register sets.** Pass `i` changes only the registers in
`W i`, setting them to `out i`, from any register file satisfying `Good` and `In i`; `Good` only
reads registers outside every `W i` and `In i` only reads `W i`. The passes over a list with
pairwise disjoint `W` run one after the other. -/
theorem seqList_passes {ι : Type} (p : ι → Pr P T Q A U) (W : ι → Fin T → Prop)
    (Good : (Fin T → List (Fin (A + 4))) → Prop) (In : ι → (Fin T → List (Fin (A + 4))) → Prop)
    (out : ι → Fin T → List (Fin (A + 4))) (c : ℕ)
    (hp : ∀ i (v : HS T Q A U) (S : Stacks T A), Good S.R → In i S.R →
      ∃ (v' : HS T Q A U) (m : ℕ) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧ m ≤ c ∧
        Exec body (p i) (mk v S) m (mk v' { S with R := R' }) ∧ (∀ k, W i k → R' k = out i k) ∧
        ∀ k, ¬ W i k → R' k = S.R k)
    (hGood : ∀ i Rg Rg', Good Rg → (∀ k, ¬ W i k → Rg' k = Rg k) → Good Rg')
    (hIn : ∀ i Rg Rg', In i Rg → (∀ k, W i k → Rg' k = Rg k) → In i Rg') :
    ∀ l : List ι, l.Pairwise (fun i i' => ∀ k, W i k → ¬ W i' k) →
      ∀ (v : HS T Q A U) (S : Stacks T A), Good S.R → (∀ i ∈ l, In i S.R) →
      ∃ (v' : HS T Q A U) (m : ℕ) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        m ≤ l.length * c + 1 ∧
        Exec body (Prog.seqList (l.map p)) (mk v S) m (mk v' { S with R := R' }) ∧
        (∀ i ∈ l, ∀ k, W i k → R' k = out i k) ∧ ∀ k, (∀ i ∈ l, ¬ W i k) → R' k = S.R k := by
  intro l
  induction l with
  | nil =>
      intro _ v S _ _
      have he := Exec.act (body := body) .done (mk v S)
      exact ⟨v, 1, S.R, rfl, by simp, by simpa [Prog.seqList] using he, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
      intro hpw v S hG hI
      rw [List.pairwise_cons] at hpw
      obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hout₁, hfr₁⟩ := hp i v S hG (hI i List.mem_cons_self)
      obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hout₂, hfr₂⟩ := ih hpw.2 v₁ { S with R := R₁ }
        (hGood i S.R R₁ hG hfr₁)
        (fun i' hi' => hIn i' S.R R₁ (hI i' (List.mem_cons_of_mem _ hi'))
          (fun k hk => hfr₁ k (fun h => hpw.1 i' hi' k h hk)))
      refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · intro i' hi' k hk
        rcases List.mem_cons.1 hi' with rfl | hi'
        · rw [hfr₂ k (fun i'' hi'' => hpw.1 i'' hi'' k hk)]
          exact hout₁ k hk
        · exact hout₂ i' hi' k hk
      · intro k hk
        rw [hfr₂ k (fun i' hi' => hk i' (List.mem_cons_of_mem _ hi'))]
        exact hfr₁ k (hk i List.mem_cons_self)

end Utils

/-! ### Active bits and sign masks -/

/-- The active bits: bit `i` at `a₀ + ρ + K i`. -/
def actMap (a₀ ρ K N n : ℕ) (hfit : ∀ i < N, a₀ + ρ + K * i < n) : Fin N → Fin n :=
  fun i => ⟨a₀ + ρ + K * i, hfit i i.2⟩

/-- Distinct active bits for `K ≥ 1`. -/
lemma actMap_injective {a₀ ρ K N n : ℕ} (hK : 1 ≤ K) (hfit : ∀ i < N, a₀ + ρ + K * i < n) :
    Function.Injective (actMap a₀ ρ K N n hfit) := by
  intro i i' h
  have h' : a₀ + ρ + K * (i : ℕ) = a₀ + ρ + K * i' := congrArg Fin.val h
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0 < K) (Nat.add_left_cancel h'))

/-- The slots selected by a vector `u`. -/
noncomputable def uPred (u : BinaryWalsh.Address m) (s : ℕ) : Bool :=
  if h : s < m then decide (u ⟨s, h⟩ = 1) else false

/-- The strided mask of `uPred u` is the mask of `u` on the active bits. -/
lemma addrBits_maskVal {a₀ ρ K k n : ℕ} (hK : 1 ≤ K) (hfit : ∀ i < m * k, a₀ + ρ + K * i < n)
    (u : BinaryWalsh.Address m) :
    addrBits n (maskVal (a₀ + ρ) K k m (uPred u)) =
      signMask (actMap a₀ ρ K (m * k) n hfit) u := by
  funext t
  have key : (maskVal (a₀ + ρ) K k m (uPred u)).testBit t = true ↔
      ∃ (j : Fin m) (c : Fin k), actMap a₀ ρ K (m * k) n hfit (bitIdx j c) = t ∧
        u j = 1 := by
    rw [testBit_maskVal hK]
    constructor
    · rintro ⟨i, hi, hp, ht⟩
      have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hi
      have hj : i / k < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
      refine ⟨⟨i / k, hj⟩, ⟨i % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
      · apply Fin.ext
        simp only [actMap, bitIdx, finProdFinEquiv, Equiv.coe_fn_mk]
        rw [ht, Nat.mod_add_div]
      · simpa [uPred, hj] using hp
    · rintro ⟨j, c, he, hj⟩
      have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; exact Fin.elim0 c
      refine ⟨c + k * j, (bitIdx j c).2, ?_, ?_⟩
      · have hd : (c.val + k * j.val) / k = j.val := by
          rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt c.2, Nat.zero_add]
        simp [uPred, hd, j.2, hj]
      · rw [← he]
        rfl
  simp only [addrBits, signMask]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

/-! ### Row split and merge -/

section Route

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The row split: route the rows of `io` by role onto the wire temporaries (each reversed), then
move every temporary onto its wire (forward order). -/
noncomputable def splitProg : Pr P (nT BReg) Q A U :=
  .seq (routeBlocks (reg .io) (fun i => reg (.wtmp (.inl (wireOf i)))) (reg .rowctr) (reg .rowtmp)
      (reg .cs) NW (roleSel NW))
    (Prog.seqList ((List.finRange NW).map fun i =>
      moveR (reg (.wtmp (.inl (wireOf i)))) (reg (.wire (.inl (wireOf i)))) id))

/-- The row merge: merge the wires by role onto `racc` (reversed), then move it onto `io`. -/
noncomputable def mergeProg : Pr P (nT BReg) Q A U :=
  .seq (mergeBlocks (fun i => reg (.wire (.inl (wireOf i)))) (reg .racc) (reg .rowctr) (reg .rowtmp)
      (reg .cs) (reg .rows) (reg .rctmp) NW (roleSel NW))
    (moveR (reg .racc) (reg .io) id)

lemma one_le_NW : 1 ≤ NW := Nat.one_le_iff_ne_zero.2 (NeZero.ne NW)

/-- Wire `wireOf d` of the bank of `Z` is row role `d` of `Z`. -/
lemma bankZ_toBank {R r n : ℕ} (Z : ZArr (Fin (NW * R) × Fin r) n) (d : Fin NW) :
    bankZ (toBank R Z) (.inl (wireOf d)) = roleArr NW R d Z := by
  funext p
  simp only [bankZ, toBank, Equiv.symm_apply_apply]

/-- Row role `d` of the array of a bank is wire `wireOf d`. -/
lemma roleArr_ofBank {R r n : ℕ} (B : NWire → ZArr (Fin R × Fin r) n) (d : Fin NW) :
    roleArr NW R d (ofBank R (unbankZ B)) = B (.inl (wireOf d)) := by
  rw [ofBank, roleArr_unroles]
  rfl

/-- **The row split.** With `io` holding the stream of `Z` (`NW R` rows), `rowctr` the row length
`2^n r w`, and `rowtmp`, the wires and their temporaries empty, the wires end holding the bank
`bankZ (toBank R Z)`; `io` ends empty and every other register as it started. -/
theorem splitProg_exec (hNW : NW ≤ A + 4) {R n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w)
    (Z : ZArr (Fin (NW * R) × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hio : S.R (reg .io) = encZ A w Z) (hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w)
    (hrt : S.R (reg .rowtmp) = []) (hwt : ∀ x, S.R (reg (.wtmp x)) = [])
    (hwi : ∀ x, S.R (reg (.wire x)) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧
      c ≤ 6 * (NW * (R * 2 ^ n * (r * w))) + 6 * (NW * R) + 2 * NW + 3 ∧
      Exec body splitProg (mk v S) c (mk v' { S with R := R' }) ∧
      R' (reg .io) = [] ∧ (∀ x : DWire, R' (reg (.wire (.inl x))) = encZ A w (bankZ (toBank R Z) (.inl x))) ∧
      ∀ k, k ≠ reg .io → (∀ x : DWire, k ≠ reg (.wire (.inl x))) → R' k = S.R k := by
  have hB : 1 ≤ 2 ^ n * r * w :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_two_pow) hr) hw
  have hlen : (encZ A w Z).length = (NW * R) * (2 ^ n * r * w) := by
    rw [length_encZ]; ring
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hctr₁, htmp₁, hdst₁, hoth₁⟩ :=
    routeBlocks_exec body (reg .io) (fun i => reg (.wtmp (.inl (wireOf i)))) (reg .rowctr) (reg .rowtmp)
      (reg .cs) NW (roleSel NW) one_le_NW hNW
      (nodup_map_reg (l := [.io, .rowctr, .rowtmp]) (by simp)) (fun d => by simp)
      (fun a b h => wireOf.injective (by simpa using h)) hB hlen hrow v S hio rfl hrt
  have hdst₁' : ∀ d, R₁ (reg (.wtmp (.inl (wireOf d)))) = (encZ A w (roleArr NW R d Z)).reverse := by
    intro d
    rw [hdst₁ d, hwt, List.append_nil, blocksTo_roles_syms]
  obtain ⟨v₂, R₂, hu₂, he₂, hds₂, hoth₂⟩ := revList_exec body
    (fun d => reg (.wtmp (.inl (wireOf d)))) (fun d => reg (.wire (.inl (wireOf d))))
    (fun d d' => reg_ne (by simp)) (fun a b h => wireOf.injective (by simpa using h))
    (fun a b h => wireOf.injective (by simpa using h)) (List.finRange NW)
    (List.nodup_finRange NW) v₁ { S with R := R₁ }
  have hsum : ((List.finRange NW).map fun d => 2 * (R₁ (reg (.wtmp (.inl (wireOf d))))).length + 2).sum =
      NW * (2 * (R * 2 ^ n * (r * w)) + 2) := by
    rw [List.map_congr_left (g := fun _ => 2 * (R * 2 ^ n * (r * w)) + 2) (fun d _ => by
      rw [hdst₁', List.length_reverse, length_encZ])]
    simp [List.map_const', List.sum_replicate]
  refine ⟨v₂, m₁ + (NW * (2 * (R * 2 ^ n * (r * w)) + 2) + 1), R₂, by rw [hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.cast he₂ (by dsimp only; rw [hsum]) rfl), ?_, ?_, ?_⟩
  · have : 4 * (NW * R * (2 ^ n * r * w)) = 4 * (NW * (R * 2 ^ n * (r * w))) := by ring
    have : NW * (2 * (R * 2 ^ n * (r * w)) + 2) = 2 * (NW * (R * 2 ^ n * (r * w))) + 2 * NW := by
      ring
    omega
  · rw [hoth₂ _ (fun d _ => ⟨reg_ne (by simp), reg_ne (by simp)⟩)]
    exact hsrc₁
  · intro x
    obtain ⟨d, rfl⟩ := wireOf.surjective x
    rw [(hds₂ d (List.mem_finRange d)).2]
    dsimp only
    rw [hdst₁', hoth₁ _ (by simp) (fun d' => reg_ne (by simp)), hwi, List.reverse_reverse,
      List.append_nil, bankZ_toBank]
  · intro k hk1 hk2
    by_cases hk3 : ∃ x : DWire, k = reg (.wtmp (.inl x))
    · obtain ⟨x, rfl⟩ := hk3
      obtain ⟨d, rfl⟩ := wireOf.surjective x
      rw [(hds₂ d (List.mem_finRange d)).1, hwt]
    push Not at hk3
    rw [hoth₂ _ (fun d _ => ⟨hk3 _, hk2 _⟩)]
    by_cases hk4 : k = reg .rowctr
    · rw [hk4]; exact hctr₁
    by_cases hk5 : k = reg .rowtmp
    · rw [hk5]; exact htmp₁.trans hrt.symm
    exact hoth₁ k (by simp [hk1, hk4, hk5]) (fun d => (hk3 _).symm)

/-- **The row merge.** With the wires holding the bank `B` (`R` rows each), `rows` holding
`NW R` symbols, `rowctr` the row length, and `rowtmp`, `rctmp`, `racc` and `io` empty, `io` ends
holding the stream of `ofBank R (unbankZ B)`; the wires end empty and every other register as
it started. -/
theorem mergeProg_exec (hNW : NW ≤ A + 4) {R n r w : ℕ} (B : NWire → ZArr (Fin R × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hwi : ∀ x : DWire, S.R (reg (.wire (.inl x))) = encZ A w (B (.inl x)))
    (hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w) (hrt : S.R (reg .rowtmp) = [])
    (hrows : (S.R (reg .rows)).length = NW * R) (hrct : S.R (reg .rctmp) = [])
    (hacc : S.R (reg .racc) = []) (hio : S.R (reg .io) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧
      c ≤ 6 * (NW * (R * 2 ^ n * (r * w))) + 8 * (NW * R) + 6 ∧
      Exec body mergeProg (mk v S) c (mk v' { S with R := R' }) ∧
      R' (reg .io) = encZ A w (ofBank R (unbankZ B)) ∧ (∀ x : DWire, R' (reg (.wire (.inl x))) = []) ∧
      ∀ k, k ≠ reg .io → (∀ x : DWire, k ≠ reg (.wire (.inl x))) → R' k = S.R k := by
  have hlen : (encZ A w (ofBank R (unbankZ B))).length = (NW * R) * (2 ^ n * r * w) := by
    rw [length_encZ]; ring
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hdst₁, hsrc₁, hctr₁, htmp₁, hcnt₁, hct₁, hoth₁⟩ :=
    mergeBlocks_exec body (fun i => reg (.wire (.inl (wireOf i)))) (reg .racc) (reg .rowctr)
      (reg .rowtmp) (reg .cs) (reg .rows) (reg .rctmp) NW (roleSel NW) one_le_NW hNW
      (nodup_map_reg (l := [.racc, .rowctr, .rowtmp, .rows, .rctmp]) (by simp))
      (fun d => by simp) (fun a b h => wireOf.injective (by simpa using h)) hlen hrow hrows
      (fun _ => []) v S
      (fun d => by rw [hwi, List.append_nil, blocksTo_roles_syms, roleArr_ofBank]) rfl hrt rfl
      hrct
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg .racc) (reg .io) (reg_ne (by simp)) id v₁
    { S with R := R₁ }
  refine ⟨v₂, _, movedR R₁ (reg .racc) (reg .io) id (R₁ (reg .racc)), by rw [hu₂, hu₁], ?_,
    Exec.seq he₁ he₂, ?_, ?_, ?_⟩
  · simp only [hdst₁, hacc, List.append_nil, List.length_reverse, hlen]
    have : 4 * (NW * R * (2 ^ n * r * w)) = 4 * (NW * (R * 2 ^ n * (r * w))) := by ring
    have : 2 * (NW * R * (2 ^ n * r * w)) = 2 * (NW * (R * 2 ^ n * (r * w))) := by ring
    omega
  · rw [movedR, Function.update_self, hdst₁, hacc,
      hoth₁ (reg .io) (by simp) (fun d => reg_ne (by simp)), hio]
    simp only [List.append_nil, List.map_id, List.reverse_reverse]
  · intro x
    obtain ⟨d, rfl⟩ := wireOf.surjective x
    rw [movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp))]
    exact hsrc₁ d
  · intro k hk1 hk2
    by_cases hk3 : k = reg .racc
    · rw [hk3, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self, hacc]
    rw [movedR, Function.update_of_ne hk1, Function.update_of_ne hk3]
    by_cases hk4 : k = reg .rowctr
    · rw [hk4]; exact hctr₁
    by_cases hk5 : k = reg .rowtmp
    · rw [hk5]; exact htmp₁.trans hrt.symm
    by_cases hk6 : k = reg .rows
    · rw [hk6]; exact hcnt₁
    by_cases hk7 : k = reg .rctmp
    · rw [hk7]; exact hct₁.trans hrct.symm
    exact hoth₁ k (by simp [hk3, hk4, hk5, hk6, hk7]) (fun d => (hk2 _).symm)

end Route

/-! ### The private centres -/

section Centres

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The stream of the zero array is the zero pair symbol, repeated. -/
lemma encZ_zero {R r n w : ℕ} :
    encZ A w (0 : ZArr (Fin R × Fin r) n) = List.replicate (R * 2 ^ n * r * w) (pairSym A false false) := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by rw [length_encZ]; ring, fun x hx => ?_⟩
  rw [encZ, coeffList_eq_map] at hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨z, ⟨p, -, rfl⟩, hz⟩ := hx
  simp only [coeffSyms, List.mem_ofFn] at hz
  obtain ⟨t, rfl⟩ := hz
  simp [red]

/-- The zero arrays on the centres, from the length of the stream of family `0`. -/
noncomputable def zeroCentres : Pr P (nT BReg) Q A U :=
  Prog.seqList ((List.finRange 8).map fun c =>
    umulSym 1 (pairSym A false false) (reg (.wire (.inl 0))) (reg (.wire (.inr c))) (reg .tmp))

/-- Clear the centres. -/
noncomputable def clearCentres : Pr P (nT BReg) Q A U :=
  Prog.seqList ((List.finRange 8).map fun c => uclear (reg (.wire (.inr c))))

/-- **The zero centres.** With family `0` holding the stream of an array with `R` rows and the
centres and `tmp` empty, every centre ends holding the stream of the zero array; every other
register ends as it started. -/
theorem zeroCentres_exec {R r n w : ℕ} (Z₀ : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (h0 : S.R (reg (.wire (.inl 0))) = encZ A w Z₀)
    (htmp : S.R (reg .tmp) = []) (hc : ∀ c, S.R (reg (.wire (.inr c))) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (m : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
      m ≤ 8 * (4 * (R * 2 ^ n * r * w) + 4) + 1 ∧
      Exec body zeroCentres (mk v S) m (mk v' { S with R := R' }) ∧
      (∀ c, R' (reg (.wire (.inr c))) = encZ A w (0 : ZArr (Fin R × Fin r) n)) ∧
      ∀ k, (∀ c, k ≠ reg (.wire (.inr c))) → R' k = S.R k := by
  obtain ⟨v', m', R', hu, hm, he, hout, hfr⟩ := seqList_passes body
    (fun c => umulSym 1 (pairSym A false false) (reg (.wire (.inl 0))) (reg (.wire (.inr c))) (reg .tmp))
    (fun c k => k = reg (.wire (.inr c)))
    (fun Rg => Rg (reg (.wire (.inl 0))) = encZ A w Z₀ ∧ Rg (reg .tmp) = [])
    (fun c Rg => Rg (reg (.wire (.inr c))) = [])
    (fun _ _ => encZ A w (0 : ZArr (Fin R × Fin r) n)) (4 * (R * 2 ^ n * r * w) + 4)
    (fun c v S hG hI => by
      obtain ⟨v₁, hu₁, he₁⟩ := umulSym_exec body 1 (pairSym A false false)
        (a := reg (.wire (.inl 0))) (b := reg (.wire (.inr c))) (t := reg .tmp)
        (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v S hG.2
      refine ⟨v₁, _, _, hu₁, ?_, he₁, fun k hk => ?_, fun k hk => Function.update_of_ne hk _ _⟩
      · rw [hG.1, length_encZ]; nlinarith
      · rw [hk, Function.update_self, hI, List.append_nil, one_mul, hG.1, length_encZ, encZ_zero]
        congr 1; ring)
    (fun c Rg Rg' hG hR => ⟨(hR _ (reg_ne (by simp))).trans hG.1, (hR _ (reg_ne (by simp))).trans hG.2⟩)
    (fun c Rg Rg' hI hR => (hR _ rfl).trans hI)
    (List.finRange 8) ((List.nodup_finRange 8).imp fun hne k hk hk' => hne (by
      rw [hk] at hk'; simpa using hk'))
    v S ⟨h0, htmp⟩ (fun c _ => hc c)
  refine ⟨v', m', R', hu, by simpa using hm, he, fun c => hout c (List.mem_finRange c) _ rfl,
    fun k hk => hfr k fun c _ h => hk c h⟩

/-- **Clearing the centres.** Every centre ends empty; every other register ends as it started. -/
theorem clearCentres_exec (N : ℕ) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hc : ∀ c, (S.R (reg (.wire (.inr c)))).length = N) :
    ∃ (v' : HS (nT BReg) Q A U) (m : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
      m ≤ 8 * (2 * N + 2) + 1 ∧
      Exec body clearCentres (mk v S) m (mk v' { S with R := R' }) ∧
      (∀ c, R' (reg (.wire (.inr c))) = []) ∧
      ∀ k, (∀ c, k ≠ reg (.wire (.inr c))) → R' k = S.R k := by
  obtain ⟨v', m', R', hu, hm, he, hout, hfr⟩ := seqList_passes body
    (fun c => uclear (reg (.wire (.inr c)))) (fun c k => k = reg (.wire (.inr c)))
    (fun _ => True) (fun c Rg => (Rg (reg (.wire (.inr c)))).length = N)
    (fun _ _ => []) (2 * N + 2)
    (fun c v S _ hI => by
      obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (reg (.wire (.inr c))) v S
      exact ⟨v₁, _, _, hu₁, by rw [hI], he₁, fun k hk => by rw [hk, Function.update_self],
        fun k hk => Function.update_of_ne hk _ _⟩)
    (fun _ _ _ _ _ => trivial) (fun c Rg Rg' hI hR => by rw [hR _ rfl]; exact hI)
    (List.finRange 8) ((List.nodup_finRange 8).imp fun hne k hk hk' => hne (by
      rw [hk] at hk'; simpa using hk'))
    v S trivial (fun c _ => hc c)
  refine ⟨v', m', R', hu, by simpa using hm, he, fun c => hout c (List.mem_finRange c) _ rfl,
    fun k hk => hfr k fun c _ h => hk c h⟩

end Centres

/-! ### Slot phases as phase passes -/

lemma pow_I_val_add (a b : ZMod 4) :
    (⟨0, 1⟩ : GaussianInt) ^ (a + b).val = (⟨0, 1⟩ : GaussianInt) ^ a.val * (⟨0, 1⟩ : GaussianInt) ^ b.val := by
  revert a b; decide

lemma prod_pow_I_val {ι : Type} (s : Finset ι) (f : ι → ZMod 4) :
    ∏ x ∈ s, (⟨0, 1⟩ : GaussianInt) ^ (f x).val = (⟨0, 1⟩ : GaussianInt) ^ (∑ x ∈ s, f x).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_I_val_add]

/-- The `Z/4` popcount of the slot mask of `i` is the sum of the bits of slot `i` over the
columns. -/
lemma sum_slotMask {k n : ℕ} {e : Fin (m * k) → Fin n} (he : Function.Injective e) (i : Fin m)
    (x : Fin n → ZMod 2) :
    ∑ t, (((signMask e (Pi.single i 1) t * x t).val : ℕ) : ZMod 4) =
      ∑ c : Fin k, BinaryPhase.bitLift (x (e (bitIdx i c))) := by
  have h1 : ∑ t, (((signMask e (Pi.single i 1) t * x t).val : ℕ) : ZMod 4) =
      ∑ t ∈ Finset.univ.image e, (((signMask e (Pi.single i 1) t * x t).val : ℕ) : ZMod 4) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have : signMask e (Pi.single i 1) t = 0 := by
      unfold signMask
      split_ifs with hex
      · obtain ⟨j, c, hjc, _⟩ := hex
        exact absurd (Finset.mem_image.2 ⟨_, Finset.mem_univ _, hjc⟩) ht
      · rfl
    rw [this, zero_mul]; rfl
  rw [h1, Finset.sum_image (fun a _ b _ hab => he hab), ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [show finProdFinEquiv (i, c) = bitIdx i c from rfl, signMask_bitIdx he, Pi.single_eq_same,
      one_mul]
    rfl
  · intro j _ hj
    rw [show finProdFinEquiv (j, c) = bitIdx j c from rfl, signMask_bitIdx he,
      Pi.single_eq_of_ne hj, zero_mul]
    rfl
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Slot phases are phase passes.** -/
lemma phaseM_eq_phaseZ {Y : Type} {k n : ℕ} {e : Fin (m * k) → Fin n} (he : Function.Injective e)
    (i : Fin m) (c : ZMod 4) (Z : ZArr Y n) :
    phaseM e i c Z = phaseZ (signMask e (Pi.single i 1)) c Z := by
  funext p
  simp only [phaseM, phaseZ, phaseExp]
  refine congrArg (· * Z p) ?_
  rw [prod_pow_I_val, ← Finset.mul_sum, sum_slotMask he]
  rfl

/-! ### Sign passes -/

/-- Rewrite register updates at distinct register names. -/
local macro "upd_simp" : tactic => `(tactic| simp only [Function.update_self, ne_eq,
  Function.update_of_ne, reg_inj, LReg.sc.injEq, LReg.ph.injEq, LReg.wire.injEq, LReg.wtmp.injEq,
  reduceCtorEq, not_false_eq_true, Fin.reduceEq, Sum.inl.injEq, Sum.inr.injEq])

section Signs

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The step bound of `expProg G F` from `u` at level `j`. -/
def expCost (G F u j : ℕ) : ℕ :=
  4 * u + 2 * j + 8 + ∑ i ∈ Finset.range j, (8 * expSeq G F u i + 12)

/-- Prepare the sign masks at level `j + 1`: `k = bits u j` on `sc 1` (the exponent program with
`G = 0`, `F = m` at level `j`), `o = a₀ + ρ` on `sc 0`, and the record count `2^n (rows / NW)` of
one wire on `ph .cnt`. -/
noncomputable def maskPrep : Pr P (nT BReg) Q A U :=
  .seq (withPred (reg .lev) (reg (.sc 5))
      (expProg 0 m (reg .u) (reg .lev) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4))))
    (.seq (ucopy (reg .a₀) (reg (.sc 0)) (reg (.sc 2)))
      (.seq (uadd (reg .ρ) (reg (.sc 0)) (reg (.sc 2)))
        (.seq (udiv NW (reg .rows) (reg (.ph .cnt)) (reg (.sc 2)))
          (upow2 (reg .n) (reg (.ph .cnt)) (reg (.sc 2)) (reg (.sc 3))))))

/-- Clear the registers of `maskPrep`. -/
noncomputable def maskClear : Pr P (nT BReg) Q A U :=
  .seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.ph .cnt))))

/-- The step bound of `maskPrep`. -/
noncomputable def maskPrepCost (u j a₀ ρ rows n : ℕ) : ℕ :=
  expCost 0 m u j + 2 + (4 * a₀ + 4) + (4 * ρ + 4) + (4 * rows + 4) +
    (4 * (2 ^ n * (rows / NW)) + 9 * n + 4)

/-- `maskPrep`: `sc 0` ends holding `a₀ + ρ` symbols, `sc 1` holding `bits u j`, `ph .cnt`
holding `2^n (rows / NW)`; every other register ends as it started. -/
theorem maskPrep_exec {j u K ρ a₀ L rows n w rw : ℕ} (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hpar : ParState S.R (j + 1) u K ρ a₀ L rows n w rw)
    (hsc : ∀ i, S.R (reg (.sc i)) = []) (hcnt : S.R (reg (.ph .cnt)) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ maskPrepCost u j a₀ ρ rows n ∧
      Exec body maskPrep (mk v S) c (mk v' { S with R := R' }) ∧
      (R' (reg (.sc 0))).length = a₀ + ρ ∧ (R' (reg (.sc 1))).length = bits u j ∧
      (R' (reg (.ph .cnt))).length = 2 ^ n * (rows / NW) ∧
      ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.sc 1) → k ≠ reg (.ph .cnt) → R' k = S.R k := by
  have hlev : (S.R (reg .lev)).length = j + 1 := hpar .lev
  obtain ⟨x, rest, hl⟩ : ∃ x rest, S.R (reg .lev) = x :: rest := by
    cases h : S.R (reg .lev) with
    | nil => rw [h] at hlev; simp at hlev
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hrest : rest.length = j := by rw [hl] at hlev; simpa using hlev
  have hu : (S.R (reg .u)).length = u := hpar .u
  -- `k` on `sc 1`
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := expProg_exec body 0 m
    (uR := reg .u) (jR := reg .lev) (eR := reg (.sc 1)) (t₁ := reg (.sc 2)) (t₂ := reg (.sc 3))
    (t₃ := reg (.sc 4)) (nodup_map_reg (l := [.u, .lev, .sc 1, .sc 2, .sc 3, .sc 4]) (by simp))
    { v with sym := some x, flag := rest.head?.isSome }
    { S with R := Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x] }
    (by upd_simp; exact hsc 1) (by upd_simp; exact hsc 2)
    (by upd_simp; exact hsc 3) (by upd_simp; exact hsc 4)
  obtain ⟨v₂, R₂, hu₂, he₂, hR₂l, hR₂t, hR₂o⟩ := withPred_exec body (reg_ne (by simp)) v S hl
    (hsc 5) he₁ (by upd_simp) (by upd_simp)
  have hR₂1 : (R₂ (reg (.sc 1))).length = bits u j := by
    rw [hR₂o _ (reg_ne (by simp)) (reg_ne (by simp))]
    upd_simp
    rw [List.length_replicate, hu, hrest, bits_eq_expSeq]
  have hR₂ : ∀ k, k ≠ reg (.sc 1) → R₂ k = S.R k := by
    intro k hk
    by_cases h1 : k = reg .lev
    · rw [h1, hR₂l]
    by_cases h2 : k = reg (.sc 5)
    · rw [h2, hR₂t]
    rw [hR₂o k h1 h2, Function.update_of_ne hk]
    dsimp only
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  -- `o` on `sc 0`
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec body (a := reg .a₀) (b := reg (.sc 0)) (t := reg (.sc 2))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (hR₂ _ (reg_ne (by simp)) |>.trans (hsc 2))
  obtain ⟨R₃, he₃, hR₃b, hR₃⟩ := exec_upd body (S := S) (R := R₂) he₃
  obtain ⟨v₄, hu₄, he₄⟩ := uadd_exec body (a := reg .ρ) (b := reg (.sc 0)) (t := reg (.sc 2))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃ { S with R := R₃ }
    ((hR₃ _ (reg_ne (by simp))).trans (hR₂ _ (reg_ne (by simp)) |>.trans (hsc 2)))
  obtain ⟨R₄, he₄, hR₄b, hR₄⟩ := exec_upd body (S := S) (R := R₃) he₄
  -- the record count on `ph .cnt`
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := udiv_exec body (c := NW) one_le_NW (a := reg .rows)
    (b := reg (.ph .cnt)) (t := reg (.sc 2)) (reg_ne (by simp)) (reg_ne (by simp))
    (reg_ne (by simp)) v₄ { S with R := R₄ }
    ((hR₄ _ (reg_ne (by simp))).trans ((hR₃ _ (reg_ne (by simp))).trans
      (hR₂ _ (reg_ne (by simp)) |>.trans (hsc 2))))
  obtain ⟨R₅, he₅, hR₅b, hR₅⟩ := exec_upd body (S := S) (R := R₄) he₅
  have hR₅o : ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.sc 1) → k ≠ reg (.ph .cnt) → R₅ k = S.R k :=
    fun k h0 h1 h2 => (hR₅ k h2).trans ((hR₄ k h0).trans ((hR₃ k h0).trans (hR₂ k h1)))
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := upow2_exec body (a := reg .n) (b := reg (.ph .cnt))
    (t₁ := reg (.sc 2)) (t₂ := reg (.sc 3))
    (nodup_map_reg (l := [.n, .ph .cnt, .sc 2, .sc 3]) (by simp)) v₅ { S with R := R₅ }
    ((hR₅o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))).trans (hsc 2))
    ((hR₅o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))).trans (hsc 3))
  obtain ⟨R₆, he₆, hR₆b, hR₆⟩ := exec_upd body (S := S) (R := R₅) he₆
  -- the contents
  have hn' : (R₅ (reg .n)).length = n :=
    (congrArg List.length (hR₅o _ (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)))).trans (hpar .n)
  have hrows' : (R₄ (reg .rows)).length = rows := by
    rw [hR₄ _ (reg_ne (by simp)), hR₃ _ (reg_ne (by simp)), hR₂ _ (reg_ne (by simp))]
    exact hpar .rows
  have hcnt₄ : R₄ (reg (.ph .cnt)) = [] := by
    rw [hR₄ _ (reg_ne (by simp)), hR₃ _ (reg_ne (by simp)), hR₂ _ (reg_ne (by simp))]
    exact hcnt
  have hcnt₅ : (R₅ (reg (.ph .cnt))).length = rows / NW := by
    rw [hR₅b]; dsimp only; rw [hcnt₄, List.append_nil, List.length_replicate, hrows']
  have ho₄ : (R₄ (reg (.sc 0))).length = a₀ + ρ := by
    rw [hR₄b]; dsimp only
    rw [hR₃b, hR₃ (reg .ρ) (reg_ne (by simp))]; dsimp only
    rw [hR₂ (reg .ρ) (reg_ne (by simp)), hR₂ (reg .a₀) (reg_ne (by simp)),
      hR₂ (reg (.sc 0)) (reg_ne (by simp)), hsc 0, List.append_nil,
      List.length_append, List.length_replicate, List.length_replicate, hpar .a₀, hpar .ρ,
      Nat.add_comm]
  have ha₀ : (R₂ (reg .a₀)).length = a₀ := by rw [hR₂ _ (reg_ne (by simp))]; exact hpar .a₀
  have hρ' : (R₃ (reg .ρ)).length = ρ := by
    rw [hR₃ _ (reg_ne (by simp)), hR₂ _ (reg_ne (by simp))]; exact hpar .ρ
  refine ⟨v₆, _, R₆, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁],
    ?_, Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))), ?_, ?_, ?_, ?_⟩
  · dsimp only at hm₁ hm₅ hm₆ ⊢
    rw [ha₀, hρ']
    rw [hrows'] at hm₅
    rw [hn', hcnt₅] at hm₆
    have hm₁' : m₁ ≤ expCost 0 m u j := by
      have e1 : Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x]
          (reg .u) = S.R (reg .u) := by
        upd_simp
      have e2 : Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x]
          (reg .lev) = rest := by
        upd_simp
      rw [e1, e2, hu, hrest] at hm₁
      exact hm₁
    unfold maskPrepCost
    omega
  · rw [hR₆ _ (reg_ne (by simp)), hR₅ _ (reg_ne (by simp))]; exact ho₄
  · rw [hR₆ _ (reg_ne (by simp)), hR₅ _ (reg_ne (by simp)), hR₄ _ (reg_ne (by simp)),
      hR₃ _ (reg_ne (by simp))]
    exact hR₂1
  · rw [hR₆b]; dsimp only; rw [length_flatMap_replicate, hcnt₅, hn']
  · intro k h0 h1 h2
    rw [hR₆ k h2, hR₅o k h0 h1 h2]

/-- `maskClear`: the three registers of `maskPrep` end empty. -/
theorem maskClear_exec (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) :
    ∃ (v' : HS (nT BReg) Q A U) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body maskClear (mk v S)
        (2 * (S.R (reg (.sc 0))).length + 2 + (2 * (S.R (reg (.sc 1))).length + 2 +
          (2 * (S.R (reg (.ph .cnt))).length + 2))) (mk v' { S with R := R' }) ∧
      R' (reg (.sc 0)) = [] ∧ R' (reg (.sc 1)) = [] ∧ R' (reg (.ph .cnt)) = [] ∧
      ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.sc 1) → k ≠ reg (.ph .cnt) → R' k = S.R k := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (reg (.sc 0)) v S
  obtain ⟨R₁, he₁, hR₁b, hR₁⟩ := exec_upd body (S := S) (R := S.R) he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body (reg (.sc 1)) v₁ { S with R := R₁ }
  obtain ⟨R₂, he₂, hR₂b, hR₂⟩ := exec_upd body (S := S) (R := R₁) he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (reg (.ph .cnt)) v₂ { S with R := R₂ }
  obtain ⟨R₃, he₃, hR₃b, hR₃⟩ := exec_upd body (S := S) (R := R₂) he₃
  have h1 : R₁ (reg (.sc 1)) = S.R (reg (.sc 1)) := hR₁ _ (reg_ne (by simp))
  have h2 : R₂ (reg (.ph .cnt)) = S.R (reg (.ph .cnt)) :=
    (hR₂ _ (reg_ne (by simp))).trans (hR₁ _ (reg_ne (by simp)))
  refine ⟨v₃, R₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃))
    (by dsimp only; rw [h1, h2]) rfl, ?_, ?_, hR₃b, ?_⟩
  · rw [hR₃ _ (reg_ne (by simp)), hR₂ _ (reg_ne (by simp)), hR₁b]
  · rw [hR₃ _ (reg_ne (by simp)), hR₂b]
  · intro k h0 h1 h2
    rw [hR₃ k h2, hR₂ k h1, hR₁ k h0]

/-- The registers read by a sign pass: `n` on `n`, `o` on `sc 0`, `K` on `K`, `k` on `sc 1`; the
other scratch registers empty; the phase registers at rest, with the record count `R 2^n` of
one wire on `ph .cnt`. -/
structure SignGood (Rg : Fin (nT BReg) → List (Fin (A + 4))) (n o K k R r w : ℕ) : Prop where
  hn : (Rg (reg .n)).length = n
  ho : (Rg (reg (.sc 0))).length = o
  hK : (Rg (reg .K)).length = K
  hk : (Rg (reg (.sc 1))).length = k
  hsc : ∀ i : Fin 6, 2 ≤ i.val → Rg (reg (.sc i)) = []
  hph : ∀ x, x ≠ .arr → x ≠ .cnt → phRest n r w x (Rg (reg (.ph x)))
  hcnt : (Rg (reg (.ph .cnt))).length = R * 2 ^ n

/-- `SignGood` does not read the wires. -/
lemma SignGood.congr {Rg Rg' : Fin (nT BReg) → List (Fin (A + 4))} {n o K k R r w : ℕ}
    (h : SignGood Rg n o K k R r w)
    (hR : ∀ x, (∀ y, x ≠ .wire y) → Rg' (reg x) = Rg (reg x)) : SignGood Rg' n o K k R r w where
  hn := by rw [hR _ (fun y => by simp)]; exact h.hn
  ho := by rw [hR _ (fun y => by simp)]; exact h.ho
  hK := by rw [hR _ (fun y => by simp)]; exact h.hK
  hk := by rw [hR _ (fun y => by simp)]; exact h.hk
  hsc i hi := by rw [hR _ (fun y => by simp)]; exact h.hsc i hi
  hph x h1 h2 := by rw [hR _ (fun y => by simp)]; exact h.hph x h1 h2
  hcnt := by rw [hR _ (fun y => by simp)]; exact h.hcnt

/-- One phase pass on the wire `x`: build the strided mask of `uPred u` on `ph .msk`, run the
phase pass with `c` on the wire, and clear the mask. -/
noncomputable def slotPass (x : NWire) (u : BinaryWalsh.Address m) (c : ZMod 4) :
    Pr P (nT BReg) Q A U :=
  .seq (strideMask (reg .n) (reg (.sc 0)) (reg .K) (reg (.sc 1)) (reg (.ph .msk)) (reg (.sc 2))
      (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5)) m (uPred u))
    (.seq (phaseProg (phMap (reg (.wire x))) (reg .st) c) (uclear (reg (.ph .msk))))

/-- The step bound of one sign pass. -/
def signCost (n o K k R r w : ℕ) : ℕ :=
  (10 * n + 4 * o + m * (k * (4 * K + 9) + 4) + 15) +
    (R * 2 ^ n * (25 * r * w + 20 * n + 36) + 33) + (2 * n + 2)

/-- **One phase pass.** The wire `x` holding the stream of `Z` ends holding the stream of
`phaseZ mask c Z`, `mask` being the strided mask of `uPred u`; every other register ends as it
started. -/
theorem slotPass_exec (hA : 5 ≤ A) {n o K k R r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K)
    (xw : NWire) (u : BinaryWalsh.Address m) (cc : ZMod 4) (mask : Fin n → ZMod 2)
    (hmask : addrBits n (maskVal o K k m (uPred u)) = mask) (Z : ZArr (Fin R × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hG : SignGood S.R n o K k R r w)
    (hX : S.R (reg (.wire xw)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ signCost n o K k R r w ∧
      Exec body (slotPass xw u cc) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire xw)) (encZ A w (phaseZ mask cc Z)) }) := by
  have hmsk : S.R (reg (.ph .msk)) = [] := hG.hph .msk (by decide) (by decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := strideMask_exec body
    (nodup_map_reg (l := [.n, .sc 0, .K, .sc 1, .ph .msk, .sc 2, .sc 3, .sc 4, .sc 5]) (by simp))
    m (uPred u) v S hG.hn hG.ho hG.hK hG.hk hK (hG.hsc 2 (by decide)) (hG.hsc 3 (by decide))
    (hG.hsc 4 (by decide)) (hG.hsc 5 (by decide))
  obtain ⟨R₁, he₁, hR₁b, hR₁⟩ := exec_upd body (S := S) (R := S.R) he₁
  have hph : ∀ x, x ≠ PhaseReg.arr → phMap (reg (BReg := BReg) (.wire xw)) x =
      reg (.ph x) := fun x hx => phMap_of_ne _ hx
  have hR₁ph : ∀ x, x ≠ .msk → R₁ (reg (.ph x)) = S.R (reg (.ph x)) :=
    fun x hx => hR₁ _ (reg_ne (by simpa using hx))
  have hP : ∀ x, x ≠ PhaseReg.arr → x ≠ .msk →
      R₁ (phMap (reg (.wire xw)) x) = S.R (reg (.ph x)) :=
    fun x h1 h2 => by rw [hph x h1, hR₁ph x h2]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := phaseProg_exec body
    (ρ := phMap (reg (.wire xw))) (st := reg .st)
    (phMap_injective (fun x => reg_ne (by simp)))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hph _ (by decide)]; exact reg_ne (by simp)))
    hA hr hw cc mask (maskVal o K k m (uPred u)) hmask Z
    (cs := S.R (reg (.ph .rc))) (ws := S.R (reg (.ph .wc))) (kk := S.R (reg (.ph .cnt)))
    (hG.hph .rc (by decide) (by decide)) (hG.hph .wc (by decide) (by decide)) hG.hcnt v₁
    { S with R := R₁ }
    (by dsimp only; rw [phMap_arr, hR₁ _ (reg_ne (by simp)), hX])
    (fun q => by
      dsimp only; rw [hP _ (by simp) (by simp)]; exact hG.hph (.cls q) (by simp) (by simp))
    (hP _ (by decide) (by decide)) (hP _ (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .tmp (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .aux (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .aux2 (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .af (by decide) (by decide))
    (by dsimp only; rw [hph _ (by decide), hR₁b, hmsk, List.append_nil])
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .t0 (by decide) (by decide))
    (by dsimp only; rw [hP _ (by decide) (by decide)]; exact hG.hph .t1 (by decide) (by decide))
    (hP _ (by decide) (by decide))
  obtain ⟨R₂, he₂, hR₂b, hR₂⟩ := exec_upd body (S := S) (R := R₁) he₂
  rw [phMap_arr] at hR₂b hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (reg (.ph .msk)) v₂ { S with R := R₂ }
  obtain ⟨R₃, he₃, hR₃b, hR₃⟩ := exec_upd body (S := S) (R := R₂) he₃
  have hR₂m : R₂ (reg (.ph .msk)) = binSyms n (maskVal o K k m (uPred u)) := by
    rw [hR₂ _ (reg_ne (by simp)), hR₁b, hmsk, List.append_nil]
  have hfin : R₃ = Function.update S.R (reg (.wire xw)) (encZ A w (phaseZ mask cc Z)) := by
    funext x
    by_cases h1 : x = reg (.wire xw)
    · rw [h1, Function.update_self, hR₃ _ (reg_ne (by simp)), hR₂b]
    rw [Function.update_of_ne h1]
    by_cases h2 : x = reg (.ph .msk)
    · rw [h2, hR₃b, hmsk]
    rw [hR₃ x h2, hR₂ x h1, hR₁ x h2]
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl
    (by rw [hfin])⟩
  dsimp only
  rw [hR₂m, length_binSyms]
  unfold signCost
  omega

/-- The slot phase instruction: prepare the masks, one phase pass on slot `i` of wire `x`, clear. -/
noncomputable def phaseInstr (x : NWire) (i : Fin m) (c : ZMod 4) : Pr P (nT BReg) Q A U :=
  .seq maskPrep (.seq (slotPass x (Pi.single i 1) c) maskClear)

/-- The step bound of the slot phase instruction at level `j + 1` on wires of `R` rows. -/
noncomputable def phaseInstrCost (u j a₀ ρ K R n r w : ℕ) : ℕ :=
  maskPrepCost u j a₀ ρ (NW * R) n + signCost n (a₀ + ρ) K (bits u j) R r w +
    (2 * (a₀ + ρ) + 2 + (2 * bits u j + 2 + (2 * (2 ^ n * R) + 2)))

/-- **The slot phase instruction.** With the parameters of level `j + 1`, every register other
than the wires at rest and the wire `x` holding the stream of `Z`, the wire `x` ends holding the
stream of `phaseM e i c Z` for the active bits `e i = a₀ + ρ + K i`; every other register ends as
it started. -/
theorem phaseInstr_exec (hA : 5 ≤ A) {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {j u K ρ a₀ L R n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K)
    (hfit : ∀ i < m * bits u j, a₀ + ρ + K * i < n) (x : NWire) (i : Fin m) (cc : ZMod 4)
    (Z : ZArr (Fin R × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (NW * R) n w (r * w))
    (hrest : RestBut bcRest n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) S.R)
    (hX : S.R (reg (.wire x)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ phaseInstrCost u j a₀ ρ K R n r w ∧
      Exec body (phaseInstr x i cc) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire x))
          (encZ A w (phaseM (k := bits u j) (actMap a₀ ρ K (m * bits u j) n hfit) i cc Z)) }) := by
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i) (by simp)
  have hcnt : S.R (reg (.ph .cnt)) = [] := hrest (.ph .cnt) (by simp)
  obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hR₁o, hR₁k, hR₁c, hR₁⟩ :=
    maskPrep_exec body v S hpar hsc hcnt
  have hdiv : NW * R / NW = R := Nat.mul_div_cancel_left R (Nat.pos_of_neZero NW)
  have hG : SignGood R₁ n (a₀ + ρ) K (bits u j) R r w := {
    hn := by
      rw [hR₁ _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]; exact hpar .n
    ho := hR₁o
    hK := by
      rw [hR₁ _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]; exact hpar .K
    hk := hR₁k
    hsc := fun i hi => by
      rw [hR₁ _ (reg_ne fun h => by rw [LReg.sc.injEq] at h; subst h; simp at hi)
        (reg_ne fun h => by rw [LReg.sc.injEq] at h; subst h; simp at hi) (reg_ne (by simp))]
      exact hsc i
    hph := fun x h1 h2 => by
      rw [hR₁ _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simpa using h2))]
      exact hrest (.ph x) (by simp)
    hcnt := by rw [hR₁c, hdiv, Nat.mul_comm] }
  set e := actMap a₀ ρ K (m * bits u j) n hfit with he
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := slotPass_exec body hA hr hw hK x (Pi.single i 1) cc _
    (addrBits_maskVal hK hfit _) Z v₁ { S with R := R₁ } hG
    (by dsimp only; rw [hR₁ _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]; exact hX)
  set R₂ := Function.update R₁ (reg (.wire x)) (encZ A w (phaseZ (signMask e (Pi.single i 1)) cc Z))
  obtain ⟨v₃, R₃, hu₃, he₃, hR₃o, hR₃k, hR₃c, hR₃⟩ := maskClear_exec body v₂ { S with R := R₂ }
  have hR₂w : ∀ k, k ≠ reg (.wire x) → R₂ k = R₁ k := fun k hk => Function.update_of_ne hk _ _
  have hfin : R₃ = Function.update S.R (reg (.wire x)) (encZ A w (phaseM e i cc Z)) := by
    funext k
    by_cases h0 : k = reg (.sc 0)
    · rw [h0, hR₃o, Function.update_of_ne (reg_ne (by simp)), hsc 0]
    by_cases h1 : k = reg (.sc 1)
    · rw [h1, hR₃k, Function.update_of_ne (reg_ne (by simp)), hsc 1]
    by_cases h2 : k = reg (.ph .cnt)
    · rw [h2, hR₃c, Function.update_of_ne (reg_ne (by simp)), hcnt]
    rw [hR₃ k h0 h1 h2]
    dsimp only
    by_cases hx : k = reg (.wire x)
    · rw [hx]
      simp only [R₂, Function.update_self]
      rw [phaseM_eq_phaseZ (actMap_injective hK hfit)]
    rw [hR₂w k hx, Function.update_of_ne hx, hR₁ k h0 h1 h2]
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl
    (by rw [hfin])⟩
  dsimp only
  rw [hR₂w _ (reg_ne (by simp)), hR₂w _ (reg_ne (by simp)), hR₂w _ (reg_ne (by simp)), hR₁o,
    hR₁k, hR₁c, hdiv]
  unfold phaseInstrCost
  omega

end Signs

/-! ### The child exponent and the instruction list -/

section Instrs

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- `Tc := expZ u ds j` at level `j + 1`: the exponent program with the gate and factor counts
of `program ds`, run with the top symbol of `lev` parked. -/
noncomputable def tcBuild (ds : ComplexFramedExecution.Directions) : Pr P (nT BReg) Q A U :=
  withPred (reg .lev) (reg (.sc 5))
    (expProg (gateCount (program ds)) (factorCount (program ds)) (reg .u) (reg .lev) (reg .Tc)
      (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)))

/-- `tcBuild`: `Tc` ends holding `expZ u ds j` symbols; every other register ends as it
started. -/
theorem tcBuild_exec (ds : ComplexFramedExecution.Directions) {j u K ρ a₀ L rows n w rw : ℕ}
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hpar : ParState S.R (j + 1) u K ρ a₀ L rows n w rw)
    (hsc : ∀ i, S.R (reg (.sc i)) = []) (hTc : S.R (reg .Tc) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧
      c ≤ expCost (gateCount (program ds)) (factorCount (program ds)) u j + 2 ∧
      Exec body (tcBuild ds) (mk v S) c (mk v' { S with R := R' }) ∧
      (R' (reg .Tc)).length = expZ u ds j ∧ ∀ k, k ≠ reg .Tc → R' k = S.R k := by
  have hlev : (S.R (reg .lev)).length = j + 1 := hpar .lev
  obtain ⟨x, rest, hl⟩ : ∃ x rest, S.R (reg .lev) = x :: rest := by
    cases h : S.R (reg .lev) with
    | nil => rw [h] at hlev; simp at hlev
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hrest : rest.length = j := by rw [hl] at hlev; simpa using hlev
  have hu : (S.R (reg .u)).length = u := hpar .u
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := expProg_exec body (gateCount (program ds))
    (factorCount (program ds))
    (uR := reg .u) (jR := reg .lev) (eR := reg .Tc) (t₁ := reg (.sc 2)) (t₂ := reg (.sc 3))
    (t₃ := reg (.sc 4)) (nodup_map_reg (l := [.u, .lev, .Tc, .sc 2, .sc 3, .sc 4]) (by simp))
    { v with sym := some x, flag := rest.head?.isSome }
    { S with R := Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x] }
    (by upd_simp; exact hTc) (by upd_simp; exact hsc 2)
    (by upd_simp; exact hsc 3) (by upd_simp; exact hsc 4)
  obtain ⟨v₂, R₂, hu₂, he₂, hR₂l, hR₂t, hR₂o⟩ := withPred_exec body (reg_ne (by simp)) v S hl
    (hsc 5) he₁ (by upd_simp) (by upd_simp)
  have e1 : Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x]
      (reg .u) = S.R (reg .u) := by
    upd_simp
  have e2 : Function.update (Function.update S.R (reg .lev) rest) (reg (.sc 5)) [x]
      (reg .lev) = rest := by
    upd_simp
  refine ⟨v₂, _, R₂, by rw [hu₂, hu₁], ?_, he₂, ?_, ?_⟩
  · dsimp only at hm₁
    rw [e1, e2, hu, hrest] at hm₁
    unfold expCost
    omega
  · rw [hR₂o _ (reg_ne (by simp)) (reg_ne (by simp))]
    upd_simp
    rw [List.length_replicate, hu, hrest, expZ_eq_expSeq]
  · intro k hk
    by_cases h1 : k = reg .lev
    · rw [h1, hR₂l]
    by_cases h2 : k = reg (.sc 5)
    · rw [h2, hR₂t]
    rw [hR₂o k h1 h2, Function.update_of_ne hk]
    dsimp only
    rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- The program of one instruction: `gateProg` on the bank for a gate, the supplied program for
a factor. -/
noncomputable def instrProg (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U) : Instr → Pr P (nT BReg) Q A U
  | .gate g => gateProg (fun v => reg (.wire v)) (fun v => reg (.wtmp v)) (reg .st) (reg .ctr)
      (reg .tmp) (reg .cS) (reg .cR) (reg .tS) (reg .tR) g
  | .factor fw g => fp fw g
  | .trans w v => mp (.trans w v)
  | .xor w i j => mp (.xor w i j)
  | .phase w i c => mp (.phase w i c)

/-- The gate layout of the bank. -/
lemma gateLayout : GateLayout (fun v => reg (BReg := BReg) (.wire v)) (fun v => reg (.wtmp v))
    (reg .st) (reg .ctr) (reg .tmp) (reg .cS) (reg .cR) (reg .tS) (reg .tR) where
  ρ_inj := fun a b h => by simpa using h
  σ_inj := fun a b h => by simpa using h
  ρ_σ _ _ := reg_ne (by simp)
  ρ_st _ := reg_ne (by simp)
  regs_nodup := nodup_map_reg (l := [.ctr, .tmp, .cS, .cR, .tS, .tR]) (by simp)
  ρ_regs _ := by simp
  σ_regs _ := by simp

/-- The step bound of one gate on wires of `R` rows. -/
noncomputable def gateCost (R n r w : ℕ) : ℕ :=
  Fintype.card NWire * (R * 2 ^ n * r) * (11 * w + 24) + 4 * Fintype.card NWire + 4

/-- **The instruction list.** From the node-internal state with the wires holding the bank `B`,
the programs of the instructions of `l ⊆ program ds` leave the wires holding
`runM e child Tc l B`, every other register as it was. -/
theorem instrs_exec (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} (hA : 4 ≤ A)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    {j u K ρ a₀ L rows n r w Tc cf cm R k : ℕ} (hw : 1 ≤ w) (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpec body (fp fw g) bcRest j u K ρ a₀ L rows n r w e child Tc fw g cf)
    (hmono : ∀ i ∈ program ds, i.IsMono →
      MonoSpec body (mp i) bcRest j u K ρ a₀ L rows n r w e child Tc i cm) :
    ∀ l : List Instr, (∀ i ∈ l, i ∈ program ds) →
      ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
      NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
      (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
      ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
        v'.user = v.user ∧
        c ≤ gateCount l * gateCost R n r w + factorCount l * cf + monoCount l * cm + 1 ∧
        Exec body (Prog.seqList (l.map (instrProg fp mp))) (mk v S) c (mk v' { S with R := R' }) ∧
        (∀ x, R' (reg (.wire x)) = encZ A w (runM e child Tc l B x)) ∧
        ∀ q, (∀ x, q ≠ reg (.wire x)) → R' q = S.R q := by
  intro l
  induction l with
  | nil =>
      intro _ B v S _ hB
      have he := Exec.act (body := body) .done (mk v S)
      exact ⟨v, 1, S.R, rfl, by simp [gateCount, factorCount, monoCount],
        by simpa [Prog.seqList] using he, hB, fun _ _ => rfl⟩
  | cons ins l ih =>
      intro hl B v S hN hB
      have hl' : ∀ i ∈ l, i ∈ program ds := fun i hi => hl i (List.mem_cons_of_mem _ hi)
      cases ins with
      | gate g =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hρ₁, hfr₁⟩ := gateProg_exec body gateLayout g hA
            (hgate g (hl _ List.mem_cons_self)) hw B v S hB
            (fun x => hN.rest (.wtmp x) (by simp)) (hN.rest .ctr (by simp))
            (hN.rest .tmp (by simp)) (hN.rest .cS (by simp)) (hN.rest .cR (by simp))
            (hN.rest .tS (by simp)) (hN.rest .tR (by simp))
          have hfr : ∀ q, (∀ x, q ≠ reg (.wire x)) → R₁ q = S.R q :=
            fun q hq => hfr₁ q (by rintro ⟨x, rfl⟩; exact hq x rfl)
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl' (gateZ g B) v₁ { S with R := R₁ }
            (hN.congr hfr) hρ₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr q hq)⟩
          have hm₁' : m₁ ≤ gateCost R n r w := hm₁
          simp only [gateCount, factorCount, monoCount, Nat.add_mul, Nat.one_mul]
          omega
      | factor fw g =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hw₁, hfr₁⟩ :=
            hfac fw g (hl _ List.mem_cons_self) B v S hN hB
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl'
            (execM e child Tc (.factor fw g) B) v₁ { S with R := R₁ } (hN.congr hfr₁) hw₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
          simp only [gateCount, factorCount, monoCount, Nat.add_mul, Nat.one_mul]
          omega
      | trans fw tv =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hw₁, hfr₁⟩ :=
            hmono _ (hl _ List.mem_cons_self) trivial B v S hN hB
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl'
            (execM e child Tc (.trans fw tv) B) v₁ { S with R := R₁ } (hN.congr hfr₁) hw₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
          simp only [gateCount, factorCount, monoCount, Nat.add_mul, Nat.one_mul]
          omega
      | xor fw i' j' =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hw₁, hfr₁⟩ :=
            hmono _ (hl _ List.mem_cons_self) trivial B v S hN hB
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl'
            (execM e child Tc (.xor fw i' j') B) v₁ { S with R := R₁ } (hN.congr hfr₁) hw₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
          simp only [gateCount, factorCount, monoCount, Nat.add_mul, Nat.one_mul]
          omega
      | phase fw i' c' =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hw₁, hfr₁⟩ :=
            hmono _ (hl _ List.mem_cons_self) trivial B v S hN hB
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl'
            (execM e child Tc (.phase fw i' c') B) v₁ { S with R := R₁ } (hN.congr hfr₁) hw₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
          simp only [gateCount, factorCount, monoCount, Nat.add_mul, Nat.one_mul]
          omega

end Instrs

/-! ### The signed exchange -/

section Exchange

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The stream of `i ^ q Z` is the stream of `Z` multiplied coefficientwise by `unitG q`. -/
lemma encZ_unit {R r n w : ℕ} (q : Fin 4) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w ((⟨0, 1⟩ : GaussianInt) ^ q.val • Z) =
      ((coeffList w Z).map (GR.mulG (unitG q).1 (unitG q).2)).flatMap (coeffSyms A w) := by
  rw [encZ, ← coeffList_map (fun z => (⟨(unitG q).1, (unitG q).2⟩ : GaussianInt) * z) _
    (fun z => red_mulG w _ _ z) Z]
  congr 2
  funext p
  rw [Pi.smul_apply, smul_eq_mul, pow_I_eq_unitG]

/-- The stream of `-Z` is the stream of `Z` negated coefficientwise. -/
lemma encZ_neg {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    encZ A w (-Z) = ((coeffList w Z).map fun z => -z).flatMap (coeffSyms A w) := by
  rw [encZ, ← coeffList_map (fun z => -z) (fun z => -z) (fun z => red_neg w z) Z]
  rfl

/-- The layout of a one-wire Gaussian automaton from `x` to `y` beside `ctr` and `tmp`. -/
lemma autoLayout_one {x y : LReg BReg} (hxy : x ≠ y) (hxc : x ≠ .ctr) (hxt : x ≠ .tmp)
    (hyc : y ≠ .ctr) (hyt : y ≠ .tmp) (hxs : x ≠ .st) :
    AutoLayout (fun _ : Fin 1 => reg x) (fun _ : Fin 1 => reg y) (reg .st) (reg .ctr)
      (reg .tmp) where
  ins_inj := Function.injective_of_subsingleton _
  outs_inj := Function.injective_of_subsingleton _
  ins_outs _ _ := reg_ne hxy
  ins_ctr _ := reg_ne hxc
  ins_tmp _ := reg_ne hxt
  outs_ctr _ := reg_ne hyc
  outs_tmp _ := reg_ne hyt
  ctr_tmp := reg_ne (by simp)
  ins_st _ := reg_ne hxs

end Exchange

/-! ### The node body -/

section Node

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- **The node body** at level `j + 1`, with the factor instructions supplied as programs `fp`
and the exact instructions as programs `mp`: the row split onto the families, the zero centres,
`Tc := expZ u ds j`, the instructions of `program ds`, clearing `Tc` and the centres, and the row
merge. -/
noncomputable def nodeBody (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U) :
    Pr P (nT BReg) Q A U :=
  .seq splitProg
    (.seq zeroCentres
      (.seq (tcBuild ds)
        (.seq (Prog.seqList ((program ds).map (instrProg fp mp)))
          (.seq (uclear (reg .Tc))
            (.seq clearCentres mergeProg)))))

/-- The step bound of the node body at level `j + 1` with `R` rows per wire (`NW R` rows on
`io`), factor programs within `cf` steps and exact instruction programs within `cm` steps. -/
noncomputable def nodeCost (ds : ComplexFramedExecution.Directions)
    (u j _K _ρ _a₀ R n r w cf cm : ℕ) : ℕ :=
  (6 * (NW * (R * 2 ^ n * (r * w))) + 6 * (NW * R) + 2 * NW + 3) +
    (8 * (4 * (R * 2 ^ n * r * w) + 4) + 1) +
    (expCost (gateCount (program ds)) (factorCount (program ds)) u j + 2) +
    (gateCount (program ds) * gateCost R n r w + factorCount (program ds) * cf +
      monoCount (program ds) * cm + 1) +
    (2 * expZ u ds j + 2) +
    (8 * (2 * (R * 2 ^ n * r * w) + 2) + 1) +
    (6 * (NW * (R * 2 ^ n * (r * w))) + 8 * (NW * R) + 6)

/-- **The node body.** From the parameters of level `j + 1` (`rows = rowsAt R₀ (j + 1)`,
`rw = r w`), every register at rest and `io` holding the stream of `Z`, and with every factor
instruction of `program ds` implemented by `fp` in the sense of `FactorSpec` and every exact
instruction by `mp` in the sense of `MonoSpec` (child semantics the layer at level `j` on the
slots, child exponent `expZ u ds j`), the node body ends with `io` holding the stream of the
level-`j + 1` layer `ofBank (rowsAt R₀ j) (nodeM e child (expZ u ds j) ds (toBank (rowsAt R₀ j) Z))`,
`e i = a₀ + ρ + K i`, every other register and `user` as before, within
`nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm` steps. -/
theorem nodeBody_exec (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w cf cm : ℕ}
    (hA : 5 ≤ A) (hNW : NW ≤ A + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (_hK : 1 ≤ K) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpec body (fp fw g) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) fw g cf)
    (hmono : ∀ i ∈ program ds, i.IsMono →
      MonoSpec body (mp i) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) i cm)
    (Z : ZArr (Fin (rowsAt R₀ (j + 1)) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A)
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w))
    (hrest : Rest bcRest n r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm ∧
      Exec body (nodeBody ds fp mp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
          (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
            (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
            (expZ u ds j) ds (toBank (rowsAt R₀ j) Z)))) }) := by
  set B₀ := bankZ (toBank (rowsAt R₀ j) Z)
  -- the row split
  have hsplit := splitProg_exec body hNW hr hw (R := rowsAt R₀ j) Z v S hio (hrest .rowctr)
    (hrest .rowtmp) (fun x => hrest (.wtmp x)) (fun x => hrest (.wire x))
  obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hio₁, hw₁, hfr₁⟩ := hsplit
  have h₁ : ∀ x : LReg BReg, x ≠ .io → (∀ y : DWire, x ≠ .wire (.inl y)) →
      R₁ (reg x) = S.R (reg x) :=
    fun x h1 h2 => hfr₁ _ (reg_ne h1) (fun y => reg_ne (h2 y))
  -- the zero centres
  obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hc₂, hfr₂⟩ := zeroCentres_exec body (B₀ (.inl 0)) v₁
    { S with R := R₁ } (hw₁ 0) (by dsimp only; rw [h₁ _ (by simp) (by simp)]; exact hrest .tmp)
    (fun c => by dsimp only; rw [h₁ _ (by simp) (by simp)]; exact hrest (.wire (.inr c)))
  have hw₂ : ∀ x, R₂ (reg (.wire x)) = encZ A w (B₀ x) := by
    intro x
    rcases x with d | c
    · rw [hfr₂ _ (fun c => reg_ne (by simp))]; exact hw₁ d
    · exact hc₂ c
  have h₂ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₂ (reg x) = S.R (reg x) :=
    fun x h1 h2 => (hfr₂ _ fun c => reg_ne (h2 _)).trans (h₁ x h1 fun y => h2 _)
  have hpar₂ : ParState R₂ (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w) :=
    hpar.congr fun x hx => h₂ x (parRegs_ne hx).1 (parRegs_ne hx).2.1
  -- the child exponent
  obtain ⟨v₃, m₃, R₃, hu₃, hm₃, he₃, hTc₃, hfr₃⟩ := tcBuild_exec body ds (j := j) v₂
    { S with R := R₂ } hpar₂
    (fun i => by dsimp only; rw [h₂ _ (by simp) (by simp)]; exact hrest (.sc i))
    (by dsimp only; rw [h₂ _ (by simp) (by simp)]; exact hrest .Tc)
  have h₃ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → x ≠ .Tc → R₃ (reg x) = S.R (reg x) :=
    fun x h1 hx hT => (hfr₃ _ (reg_ne hT)).trans (h₂ x h1 hx)
  -- the instructions
  have hN₃ : NodeRegs bcRest R₃ j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (expZ u ds j) :=
    { par := hpar.congr fun x hx => h₃ x (parRegs_ne hx).1 (parRegs_ne hx).2.1 (parRegs_ne hx).2.2
      rest := hrest.restBut_of_frame _ fun x hx hx' => by
        rw [h₃ x hx (fun y h => hx' (Or.inl ⟨y, h⟩)) (fun h => hx' (Or.inr h))]
      io := by
        rw [hfr₃ _ (reg_ne (by simp))]; dsimp only; rw [hfr₂ _ (fun c => reg_ne (by simp))]
        exact hio₁
      tc := hTc₃ }
  obtain ⟨v₄, m₄, R₄, hu₄, hm₄, he₄, hw₄, hfr₄⟩ := instrs_exec body ds fp mp (by omega) hgate
    (k := bits u j) hw (actMap a₀ ρ K (bits u (j + 1)) n hfit)
    (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c)) hfac
    hmono (program ds) (fun i hi => hi) B₀ v₃ { S with R := R₃ } hN₃
    (fun x => by dsimp only; rw [hfr₃ _ (reg_ne (by simp))]; exact hw₂ x)
  set Bf := runM (actMap a₀ ρ K (bits u (j + 1)) n hfit)
    (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
    (expZ u ds j) (program ds) B₀
  -- clearing `Tc`
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body (reg .Tc) v₄ { S with R := R₄ }
  obtain ⟨R₅, he₅, hR₅b, hR₅⟩ := exec_upd body (S := S) (R := R₄) he₅
  have h₅ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₅ (reg x) = S.R (reg x) := by
    intro x h1 hx
    by_cases hT : x = .Tc
    · subst hT
      rw [hR₅b]
      exact (hrest .Tc).symm
    · rw [hR₅ _ (reg_ne hT), hfr₄ _ (fun y => reg_ne (hx y))]
      exact h₃ x h1 hx hT
  have hw₅ : ∀ x, R₅ (reg (.wire x)) = encZ A w (Bf x) := fun x => by
    rw [hR₅ _ (reg_ne (by simp))]; exact hw₄ x
  have hio₅ : R₅ (reg .io) = [] := by
    rw [hR₅ _ (reg_ne (by simp)), hfr₄ _ (fun y => reg_ne (by simp))]; exact hN₃.io
  -- clearing the centres
  obtain ⟨v₆, m₆, R₆, hu₆, hm₆, he₆, hc₆, hfr₆⟩ := clearCentres_exec body
    (rowsAt R₀ j * 2 ^ n * r * w) v₅ { S with R := R₅ }
    (fun c => by dsimp only; rw [hw₅, length_encZ]; ring)
  dsimp only at hc₆ hfr₆
  -- the row merge
  obtain ⟨v₈, m₈, R₈, hu₈, hm₈, he₈, hio₈, hw₈, hfr₈⟩ := mergeProg_exec body hNW
    (R := rowsAt R₀ j) Bf v₆ { S with R := R₆ }
    (fun d => by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp))]; exact hw₅ _)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₅ _ (by simp) (by simp)];
        exact hrest .rowctr)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₅ _ (by simp) (by simp)];
        exact hrest .rowtmp)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₅ _ (by simp) (by simp)];
        exact hpar .rows)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₅ _ (by simp) (by simp)];
        exact hrest .rctmp)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₅ _ (by simp) (by simp)];
        exact hrest .racc)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp))]; exact hio₅)
  dsimp only at hio₈ hw₈ hfr₈
  -- the final registers
  have hfin : R₈ = Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
      (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) ds (toBank (rowsAt R₀ j) Z)))) := by
    funext q
    by_cases hq : q = reg .io
    · rw [hq, Function.update_self, hio₈]
      rfl
    rw [Function.update_of_ne hq]
    by_cases hqw : ∃ d : DWire, q = reg (.wire (.inl d))
    · obtain ⟨d, rfl⟩ := hqw
      rw [hw₈ d]
      exact (hrest (.wire (.inl d))).symm
    push Not at hqw
    rw [hfr₈ q hq hqw]
    by_cases hqc : ∃ c, q = reg (.wire (.inr c))
    · obtain ⟨c, rfl⟩ := hqc
      rw [hc₆ c]
      exact (hrest (.wire (.inr c))).symm
    push Not at hqc
    rw [hfr₆ q hqc]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective q
    refine h₅ x (fun h => hq (by rw [h]; rfl)) fun y h => ?_
    rcases y with d | c
    · exact hqw d (by rw [h]; rfl)
    · exact hqc c (by rw [h]; rfl)
  have hTc₄ : (R₄ (reg .Tc)).length = expZ u ds j := by
    rw [hfr₄ _ (fun y => reg_ne (by simp))]; exact hTc₃
  refine ⟨v₈, m₁ + (m₂ + (m₃ + (m₄ + ((2 * (R₄ (reg .Tc)).length + 2) + (m₆ + m₈))))),
    by rw [hu₈, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ he₈)))))) rfl (by rw [hfin])⟩
  rw [hTc₄]
  unfold nodeCost
  omega

/-- `nodeBody_exec` with the result written as the level-`j + 1` layer `layerZ`. -/
theorem nodeBody_exec_layerZ (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w cf cm : ℕ}
    (hA : 5 ≤ A) (hNW : NW ≤ A + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpec body (fp fw g) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) fw g cf)
    (hmono : ∀ i ∈ program ds, i.IsMono →
      MonoSpec body (mp i) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) i cm)
    (Z : ZArr (Fin (rowsAt R₀ (j + 1)) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A)
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w))
    (hrest : Rest bcRest n r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm ∧
      Exec body (nodeBody ds fp mp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (layerZ u ds R₀ (j + 1) (actMap a₀ ρ K (bits u (j + 1)) n hfit) Z)) }) :=
  nodeBody_exec body ds fp mp hA hNW hgate hr hw hK hfit hfac hmono Z v S hpar hrest hio

end Node

end IntegerMultBounds.MathlibTM2.LayerMachine
