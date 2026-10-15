module

public import IntegerMultBounds.MathlibTM2.Node.Factor

/-!
# The layer procedure

The layer machine runs one recursive procedure, `LProc.layer`, with body `layerBody hQ ds`:
`peekR lev`, then the leaf `leafP` when `lev` is empty and the node
`nodeBody ds (factorProg hQ (.call .layer) ds)` otherwise; `layerTable hQ ds` is the procedure
table. Registers: `LReg CReg`, the basis-change registers `bc x` at rest (`bcRestC Gd`: all empty
except the digit width `Gd`).

**Parameters.** At level `j` the parameter registers hold `j` (`lev`), `u`, `K`, `ρ`, `a₀`,
`L = K · bits u j` (the width of the active region), `rows = rowsAt R₀ j`, `n`, `w` and `r w`.
A factor with pivot `s` at level `j + 1` calls its child with `L / m`, `rows / NW`,
`a₀ + s · (L / m)` and `lev` without its top symbol (`Node/Factor.lean`).

**The leaf** (`leafP`, `leafP_exec`): `a₀ + ρ` on `sc 0`, the mask `binSyms n (2 ^ (a₀ + ρ))`
(`bitMask`), the stride `K`, the pass count `u` and the record count `2^n R₀` on the leaf registers
(`ucopy`, `upow2`); `leafProg`, with the array role on `io` (`leafReg`), applies the doubled
kernels on the bits `a₀ + ρ + K i`, `i < u`, which is the layer at level `0` (`k2l_eq_k2s`); the
leaf registers and `sc 0` are cleared.

**The node on empty left stacks** (`instrs_execL`, `nodeBody_execL`, `nodeBody_execL_layerZ`):
`instrs_exec` and `nodeBody_exec` of `Node/Body.lean` with every left stack empty and the factor
programs specified by `FactorSpecL`. The node never writes the left stacks, so they stay empty
before every instruction.

**Cost.** `layerCost T ds u K ρ R₀ n r w j a₀` is `leafCost … + 4` at level `0` and
`nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf + 4` at level `j + 1`, where `cf` is the largest
`factorCost` over the factors `(fw, g)` of `program ds` (`facMax`), each with the cost
`layerCost … j (a₀ + pivotOf g.2 · K · bits u j)` of the call of its child; the `4` counts the call,
the peek and the dispatch.

**Main theorem** (`layer_exec`, by induction on `j`; `layer_callSpec` restates it as `CallSpec`).
From the parameters of level `j`, every register at rest, every left stack empty and `io` holding
`encZ A w Z`, the call of the layer procedure ends with `io` holding
`encZ A w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) n hfit) Z)`, every other register and `user`
as before, within `layerCost (nT CReg) ds u K ρ R₀ n r w j a₀` steps. The level-`j + 1` case is
`nodeBody_execL_layerZ` with `factorProg_spec` for every factor, whose child calls are the
induction hypothesis at level `j`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false

/-- Evaluate register updates at register names. -/
local macro "fupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj, reduceCtorEq,
  ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.wire.injEq, LReg.wtmp.injEq, LReg.bc.injEq,
  LReg.ph.injEq, LReg.lf.injEq, IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue, movedR,
  List.map_id, id]) <;> try rfl)

/-! ### The node body on empty left stacks -/

section NodeL

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- **The instruction list on empty left stacks** (`instrs_exec` with `FactorSpecL`). From the
node-internal state with every left stack empty and the wires holding the bank `B`, the programs
of the instructions of `l ⊆ program ds` leave the wires holding `runM e child Tc l B`, every other
register as it was. -/
theorem instrs_execL (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} (hA : 4 ≤ A)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    {j u K ρ a₀ L rows n r w Tc cf R k : ℕ} (hw : 1 ≤ w) (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpecL body (fp fw g) bcRest j u K ρ a₀ L rows n r w e child Tc fw g cf) :
    ∀ l : List Instr, (∀ i ∈ l, i ∈ program ds) →
      ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
      (∀ y, S.L y = []) → NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
      (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
      ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
        v'.user = v.user ∧ c ≤ gateCount l * gateCost R n r w + factorCount l * cf + 1 ∧
        Exec body (Prog.seqList (l.map (instrProg fp))) (mk v S) c (mk v' { S with R := R' }) ∧
        (∀ x, R' (reg (.wire x)) = encZ A w (runM e child Tc l B x)) ∧
        ∀ q, (∀ x, q ≠ reg (.wire x)) → R' q = S.R q := by
  intro l
  induction l with
  | nil =>
      intro _ B v S _ _ hB
      have he := Exec.act (body := body) .done (mk v S)
      exact ⟨v, 1, S.R, rfl, by simp [gateCount, factorCount],
        by simpa [Prog.seqList] using he, hB, fun _ _ => rfl⟩
  | cons ins l ih =>
      intro hl B v S hL hN hB
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
            hL (hN.congr hfr) hρ₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr q hq)⟩
          have hm₁' : m₁ ≤ gateCost R n r w := hm₁
          simp only [gateCount, factorCount, Nat.add_mul, Nat.one_mul]
          omega
      | factor fw g =>
          obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hw₁, hfr₁⟩ :=
            hfac fw g (hl _ List.mem_cons_self) B v S hL hN hB
          obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := ih hl'
            (execM e child Tc (.factor fw g) B) v₁ { S with R := R₁ } hL (hN.congr hfr₁) hw₁
          refine ⟨v₂, m₁ + m₂, R₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hw₂,
            fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
          simp only [gateCount, factorCount, Nat.add_mul, Nat.one_mul]
          omega


/-- **The node body on empty left stacks** (`nodeBody_exec` with `FactorSpecL`). From the
parameters of level `j + 1` (`rows = rowsAt R₀ (j + 1)`, `rw = r w`), every register at rest, every
left stack empty and `io` holding the stream of `Z`, and with every factor instruction of
`program ds` implemented by `fp` in the sense of `FactorSpecL` (child semantics
the layer at level `j` on the slots, child exponent `expZ u ds j`), the node body ends with `io`
holding the stream of the level-`j + 1` layer
`ofBank (rowsAt R₀ j) (nodeM e child (expZ u ds j) ds (toBank (rowsAt R₀ j) Z))`,
`e i = a₀ + ρ + K i`, every other register and `user` as before, within
`nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf` steps. -/
theorem nodeBody_execL (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w cf : ℕ}
    (hA : 5 ≤ A) (hNW : NW ≤ A + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpecL body (fp fw g) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) fw g cf)
    (Z : ZArr (Fin (rowsAt R₀ (j + 1)) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w))
    (hrest : Rest bcRest n r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf ∧
      Exec body (nodeBody ds fp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
          (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
            (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
            (expZ u ds j) ds (toBank (rowsAt R₀ j) Z)))) }) := by
  -- the row split
  have hsplit := splitProg_exec body hNW hr hw (R := rowsAt R₀ j) Z v S hio (hrest .rowctr)
    (hrest .rowtmp) (fun x => hrest (.wtmp x)) (fun x => hrest (.wire x))
  obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hio₁, hw₁, hfr₁⟩ := hsplit
  have h₁ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₁ (reg x) = S.R (reg x) :=
    fun x h1 h2 => hfr₁ _ (reg_ne h1) (fun y => reg_ne (h2 y))
  have hpar₁ : ParState R₁ (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w) :=
    hpar.congr fun x hx => h₁ x (parRegs_ne hx).1 (parRegs_ne hx).2.1
  -- the source signs
  obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hw₂, hfr₂⟩ := signStage_exec body hA hr hw hK hfit
    (bankZ (toBank (rowsAt R₀ j) Z)) v₁ { S with R := R₁ } hpar₁
    (hrest.restBut_of_frame _ fun x hx hx' => h₁ x hx fun y h => hx' ⟨y, h⟩) hw₁
  have h₂ : ∀ x : LReg BReg, (∀ y, x ≠ .wire y) → R₂ (reg x) = R₁ (reg x) :=
    fun x hx => hfr₂ _ fun y => reg_ne (hx y)
  -- the child exponent
  obtain ⟨v₃, m₃, R₃, hu₃, hm₃, he₃, hTc₃, hfr₃⟩ := tcBuild_exec body ds (j := j) v₂
    { S with R := R₂ } (hpar₁.congr fun x hx => h₂ x (parRegs_ne hx).2.1)
    (fun i => by
      dsimp only; rw [h₂ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest (.sc i))
    (by dsimp only; rw [h₂ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest .Tc)
  have h₃ : ∀ x : LReg BReg, (∀ y, x ≠ .wire y) → x ≠ .Tc → R₃ (reg x) = R₁ (reg x) :=
    fun x hx hT => (hfr₃ _ (reg_ne hT)).trans (h₂ x hx)
  -- the instructions
  have hN₃ : NodeRegs bcRest R₃ j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (expZ u ds j) :=
    { par := hpar₁.congr fun x hx => h₃ x (parRegs_ne hx).2.1 (parRegs_ne hx).2.2
      rest := hrest.restBut_of_frame _ fun x hx hx' => by
        rw [h₃ x (fun y h => hx' (Or.inl ⟨y, h⟩)) (fun h => hx' (Or.inr h))]
        exact h₁ x hx fun y h => hx' (Or.inl ⟨y, h⟩)
      io := by rw [h₃ _ (by simp) (by simp)]; exact hio₁
      tc := hTc₃ }
  obtain ⟨v₄, m₄, R₄, hu₄, hm₄, he₄, hw₄, hfr₄⟩ := instrs_execL body ds fp (by omega) hgate
    (k := bits u j) hw (actMap a₀ ρ K (bits u (j + 1)) n hfit)
    (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c)) hfac
    (program ds) (fun i hi => hi)
    (corrInM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
      (bankZ (toBank (rowsAt R₀ j) Z))) v₃ { S with R := R₃ } hL hN₃
    (fun x => by dsimp only; rw [hfr₃ _ (reg_ne (by simp))]; exact hw₂ x)
  -- clearing `Tc`
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body (reg .Tc) v₄ { S with R := R₄ }
  obtain ⟨R₅, he₅, hR₅b, hR₅⟩ := exec_upd body (S := S) (R := R₄) he₅
  have h₅ : ∀ x : LReg BReg, (∀ y, x ≠ .wire y) → R₅ (reg x) = R₁ (reg x) := by
    intro x hx
    by_cases hT : x = .Tc
    · subst hT
      rw [hR₅b, h₁ _ (by simp) (by simp)]
      exact (hrest .Tc).symm
    · rw [hR₅ _ (reg_ne hT), hfr₄ _ (fun y => reg_ne (hx y))]
      exact h₃ x hx hT
  have h₅S : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₅ (reg x) = S.R (reg x) :=
    fun x h1 h2 => (h₅ x h2).trans (h₁ x h1 h2)
  -- the signed exchange
  obtain ⟨v₆, m₆, R₆, hu₆, hm₆, he₆, hw₆, hfr₆⟩ := exchStage_exec body hA hw (u := u)
    (runM (actMap a₀ ρ K (bits u (j + 1)) n hfit)
      (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
      (expZ u ds j) (program ds)
      (corrInM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (bankZ (toBank (rowsAt R₀ j) Z)))) v₅ { S with R := R₅ }
    (by dsimp only; rw [h₅S _ (by simp) (by simp)]; exact hrest .ctr)
    (by dsimp only; rw [h₅S _ (by simp) (by simp)]; exact hrest .tmp)
    (by dsimp only; rw [h₅S _ (by simp) (by simp)]; exact hpar .u)
    (by dsimp only; rw [h₅S _ (by simp) (by simp)]; exact hrest (.sc 0))
    (fun x => by dsimp only; rw [h₅S _ (by simp) (by simp)]; exact hrest (.wtmp x))
    (fun x => by dsimp only; rw [hR₅ _ (reg_ne (by simp))]; exact hw₄ x)
  have h₆ : ∀ x : LReg BReg, (∀ y, x ≠ .wire y) → R₆ (reg x) = R₁ (reg x) :=
    fun x hx => (hfr₆ _ fun y => reg_ne (hx y)).trans (h₅ x hx)
  -- the sink signs
  obtain ⟨v₇, m₇, R₇, hu₇, hm₇, he₇, hw₇, hfr₇⟩ := signStage_exec body hA hr hw hK hfit _ v₆
    { S with R := R₆ } (hpar₁.congr fun x hx => h₆ x (parRegs_ne hx).2.1)
    (hrest.restBut_of_frame _ fun x hx hx' => (h₆ x fun y h => hx' ⟨y, h⟩).trans
      (h₁ x hx fun y h => hx' ⟨y, h⟩)) hw₆
  have h₇ : ∀ x : LReg BReg, (∀ y, x ≠ .wire y) → R₇ (reg x) = R₁ (reg x) :=
    fun x hx => (hfr₇ _ fun y => reg_ne (hx y)).trans (h₆ x hx)
  -- the row merge
  obtain ⟨v₈, m₈, R₈, hu₈, hm₈, he₈, hio₈, hw₈, hfr₈⟩ := mergeProg_exec body hNW
    (R := rowsAt R₀ j) _ v₇ { S with R := R₇ } hw₇
    (by dsimp only; rw [h₇ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest .rowctr)
    (by dsimp only; rw [h₇ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest .rowtmp)
    (by dsimp only; rw [h₇ _ (by simp), h₁ _ (by simp) (by simp)]; exact hpar .rows)
    (by dsimp only; rw [h₇ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest .rctmp)
    (by dsimp only; rw [h₇ _ (by simp), h₁ _ (by simp) (by simp)]; exact hrest .racc)
    (by dsimp only; rw [h₇ _ (by simp)]; exact hio₁)
  -- the final registers
  have hc : (⟨0, 1⟩ : GaussianInt) ^ ((3 * (u % 4)) % 4) =
      (⟨0, 1⟩ : GaussianInt) ^ (27 * bits u j) := by
    rw [pow_I_27, bits_mod_four]
  have hfin : R₈ = Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
      (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) ds (toBank (rowsAt R₀ j) Z)))) := by
    funext q
    by_cases hq : q = reg .io
    · rw [hq, Function.update_self, hio₈, hc, corrInM_exchZ]
      rfl
    rw [Function.update_of_ne hq]
    by_cases hqw : ∃ x, q = reg (.wire x)
    · obtain ⟨x, rfl⟩ := hqw
      rw [hw₈ x]
      exact (hrest (.wire x)).symm
    push Not at hqw
    rw [hfr₈ q hq hqw]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective q
    exact (h₇ x fun y h => hqw y (by rw [h]; rfl)).trans
      (h₁ x (fun h => hq (by rw [h]; rfl)) fun y h => hqw y (by rw [h]; rfl))
  have hTc₄ : (R₄ (reg .Tc)).length = expZ u ds j := by
    rw [hfr₄ _ (fun y => reg_ne (by simp))]; exact hTc₃
  refine ⟨v₈, m₁ + (m₂ + (m₃ + (m₄ + ((2 * (R₄ (reg .Tc)).length + 2) + (m₆ + (m₇ + m₈)))))),
    by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ he₈))))))) rfl (by rw [hfin])⟩
  rw [hTc₄]
  unfold nodeCost
  omega

/-- `nodeBody_execL` with the result written as the level-`j + 1` layer `layerZ`. -/
theorem nodeBody_execL_layerZ (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w cf : ℕ}
    (hA : 5 ≤ A) (hNW : NW ≤ A + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpecL body (fp fw g) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit)
        (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
        (expZ u ds j) fw g cf)
    (Z : ZArr (Fin (rowsAt R₀ (j + 1)) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w))
    (hrest : Rest bcRest n r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf ∧
      Exec body (nodeBody ds fp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (layerZ u ds R₀ (j + 1) (actMap a₀ ρ K (bits u (j + 1)) n hfit) Z)) }) :=
  nodeBody_execL body ds fp hA hNW hgate hr hw hK hfit hfac Z v S hL hpar hrest hio

end NodeL

/-! ### The leaf -/

section Leaf

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The leaf registers on the layer machine: the array role on `io`, every other leaf register
`x` on `lf x`. -/
noncomputable def leafReg (x : IntegerMultBounds.MathlibTM2.Node.LReg) : Fin (nT BReg) :=
  if x = .k .arr then reg .io else reg (.lf x)

lemma leafReg_of_ne {x : IntegerMultBounds.MathlibTM2.Node.LReg} (hx : x ≠ .k .arr) :
    leafReg (BReg := BReg) x = reg (.lf x) := by
  simp [leafReg, hx]

lemma leafReg_arr : leafReg (BReg := BReg) (.k .arr) = reg .io := by simp [leafReg]

lemma leafReg_injective : Function.Injective (leafReg (BReg := BReg)) := by
  intro x y h
  by_cases hx : x = .k .arr <;> by_cases hy : y = .k .arr
  · rw [hx, hy]
  · rw [hx, leafReg_arr, leafReg_of_ne hy] at h; exact absurd (reg_injective h) (by simp)
  · rw [hy, leafReg_arr, leafReg_of_ne hx] at h; exact absurd (reg_injective h) (by simp)
  · rw [leafReg_of_ne hx, leafReg_of_ne hy] at h
    simpa using h

/-- **The leaf of the layer machine**: the mask `binSyms n (2 ^ (a₀ + ρ))`, the stride `K`, the
pass count `u` and the record count `2^n rows` on the leaf registers (`bitMask`, `ucopy`,
`upow2`, with `a₀ + ρ` on `sc 0`); `leafProg` on `io`; the leaf registers and `sc 0` cleared. -/
noncomputable def leafP : Pr P (nT BReg) Q A U :=
  .seq (ucopy (reg .a₀) (reg (.sc 0)) (reg (.sc 1)))
  (.seq (uadd (reg .ρ) (reg (.sc 0)) (reg (.sc 1)))
  (.seq (bitMask (reg .n) (reg (.sc 0)) (reg (.lf (.k .mask))) (reg (.sc 2)) (reg (.sc 3))
    (reg (.sc 4)))
  (.seq (ucopy (reg .K) (reg (.lf .kr)) (reg (.sc 1)))
  (.seq (ucopy (reg .u) (reg (.lf .ur)) (reg (.sc 1)))
  (.seq (ucopy (reg .rows) (reg (.lf (.k .cnt))) (reg (.sc 1)))
  (.seq (upow2 (reg .n) (reg (.lf (.k .cnt))) (reg (.sc 1)) (reg (.sc 2)))
  (.seq (leafProg leafReg)
  (.seq (uclear (reg (.lf (.k .mask))))
  (.seq (uclear (reg (.lf .kr)))
  (.seq (uclear (reg (.lf .ur)))
  (.seq (uclear (reg (.lf (.k .cnt))))
    (uclear (reg (.sc 0))))))))))))))

/-- The step bound of `leafP` on an array of `R₀` rows. -/
def leafCost (u K ρ a₀ R₀ n r w : ℕ) : ℕ :=
  (4 * a₀ + 4) + (4 * ρ + 4) + (10 * n + 4 * (ρ + a₀) + 15) + (4 * K + 4) + (4 * u + 4) +
    (4 * R₀ + 4) + (4 * (2 ^ n * R₀) + 9 * n + 4) +
    (u * (R₀ * 2 ^ n * (29 * r * w + 20 * n + 36) + 10 * n + 33) + 4) +
    (2 * n + 2) + (2 * K + 2) + (2 * u + 2) + (2 * (2 ^ n * R₀) + 2) + (2 * (ρ + a₀) + 2)

/-- The doubled kernels `k2l` of the leaf are the kernels `k2s` of the layer. -/
lemma k2l_eq_k2s {R r n : ℕ} : ∀ (l : List (Fin n)) (f : ZArr (Fin R × Fin r) n), k2l l f = k2s l f
  | [], _ => rfl
  | t :: ts, f => k2l_eq_k2s ts (k2 t f)

/-- **The leaf.** From the parameters of level `0` (`rows = R₀`), every register at rest and `io`
holding the stream of `Z`, `leafP` leaves on `io` the stream of the layer at level `0`: the
doubled kernels on the bits `a₀ + ρ + K i`, `i < u`. Every other register ends as it started. -/
theorem leafP_exec (hA : 9 ^ 4 ≤ A + 4) {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {u K ρ a₀ L R₀ n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hfit : ∀ i < u, a₀ + ρ + K * i < n) (Z : ZArr (Fin R₀ × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hpar : ParState S.R 0 u K ρ a₀ L R₀ n w (r * w)) (hrest : Rest bcRest n r w S.R)
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ leafCost u K ρ a₀ R₀ n r w ∧
      Exec body leafP (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (k2s ((List.finRange u).map (actMap a₀ ρ K u n hfit)) Z)) }) := by
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i)
  -- `a₀ + ρ` on `sc 0`
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := reg .a₀) (b := reg (.sc 0)) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v S (hs 1)
  obtain ⟨R₁, he₁, h1b, h1o⟩ := exec_upd body (S := S) (R := S.R) he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uadd_exec body (a := reg .ρ) (b := reg (.sc 0)) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    ((h1o (reg (.sc 1)) (reg_ne (by simp))).trans (hs 1))
  obtain ⟨R₂, he₂, h2b, h2o⟩ := exec_upd body (S := S) (R := R₁) he₂
  dsimp only at h2b
  have h2s : (R₂ (reg (.sc 0))).length = ρ + a₀ := by
    rw [h2b, List.length_append, List.length_replicate, h1o (reg .ρ) (reg_ne (by simp)), h1b,
      List.length_append, List.length_replicate, hs 0, hpar .ρ, hpar .a₀]
    rfl
  have h2f : ∀ k, k ≠ reg (.sc 0) → R₂ k = S.R k := fun k hk => (h2o k hk).trans (h1o k hk)
  -- the mask
  obtain ⟨v₃, hu₃, he₃⟩ := bitMask_exec body (nR := reg .n) (tR := reg (.sc 0))
    (z := reg (.lf (.k .mask))) (cnt := reg (.sc 2)) (w := reg (.sc 3)) (t₁ := reg (.sc 4))
    (n := n) (t := ρ + a₀)
    (nodup_map_reg (l := [.n, .sc 0, .lf (.k .mask), .sc 2, .sc 3, .sc 4]) (by simp)) v₂
    { S with R := R₂ }
    (by dsimp only; rw [h2f (reg .n) (reg_ne (by simp))]; exact hpar .n) h2s
    (by dsimp only; rw [h2f (reg (.sc 2)) (reg_ne (by simp))]; exact hs 2)
    (by dsimp only; rw [h2f (reg (.sc 3)) (reg_ne (by simp))]; exact hs 3)
    (by dsimp only; rw [h2f (reg (.sc 4)) (reg_ne (by simp))]; exact hs 4)
  obtain ⟨R₃, he₃, h3b, h3o⟩ := exec_upd body (S := S) (R := R₂) he₃
  dsimp only at h3b
  have h3m : R₃ (reg (.lf (.k .mask))) = binSyms n (2 ^ (ρ + a₀)) := by
    rw [h3b, h2f (reg (.lf (.k .mask))) (reg_ne (by simp)), hrest (.lf (.k .mask)),
      List.append_nil]
  have h3f : ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.lf (.k .mask)) → R₃ k = S.R k :=
    fun k h1 h2 => (h3o k h2).trans (h2f k h1)
  -- the stride, the pass count and the record count
  obtain ⟨v₄, hu₄, he₄⟩ := ucopy_exec body (a := reg .K) (b := reg (.lf .kr)) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃ { S with R := R₃ }
    ((h3f (reg (.sc 1)) (reg_ne (by simp)) (reg_ne (by simp))).trans (hs 1))
  obtain ⟨R₄, he₄, h4b, h4o⟩ := exec_upd body (S := S) (R := R₃) he₄
  dsimp only at h4b
  obtain ⟨v₅, hu₅, he₅⟩ := ucopy_exec body (a := reg .u) (b := reg (.lf .ur)) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    ((h4o (reg (.sc 1)) (reg_ne (by simp))).trans
      ((h3f (reg (.sc 1)) (reg_ne (by simp)) (reg_ne (by simp))).trans (hs 1)))
  obtain ⟨R₅, he₅, h5b, h5o⟩ := exec_upd body (S := S) (R := R₄) he₅
  dsimp only at h5b
  obtain ⟨v₆, hu₆, he₆⟩ := ucopy_exec body (a := reg .rows) (b := reg (.lf (.k .cnt)))
    (t := reg (.sc 1)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₅
    { S with R := R₅ } ((h5o (reg (.sc 1)) (reg_ne (by simp))).trans
      ((h4o (reg (.sc 1)) (reg_ne (by simp))).trans
        ((h3f (reg (.sc 1)) (reg_ne (by simp)) (reg_ne (by simp))).trans (hs 1))))
  obtain ⟨R₆, he₆, h6b, h6o⟩ := exec_upd body (S := S) (R := R₅) he₆
  dsimp only at h6b
  have h6f : ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.lf (.k .mask)) → k ≠ reg (.lf .kr) →
      k ≠ reg (.lf .ur) → k ≠ reg (.lf (.k .cnt)) → R₆ k = S.R k := fun k h1 h2 h3 h4 h5 =>
    (h6o k h5).trans ((h5o k h4).trans ((h4o k h3).trans (h3f k h1 h2)))
  have h6x : ∀ x : LReg BReg, x ≠ .sc 0 → x ≠ .lf (.k .mask) → x ≠ .lf .kr → x ≠ .lf .ur →
      x ≠ .lf (.k .cnt) → R₆ (reg x) = S.R (reg x) := fun x h1 h2 h3 h4 h5 =>
    h6f _ (reg_ne h1) (reg_ne h2) (reg_ne h3) (reg_ne h4) (reg_ne h5)
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := upow2_exec body (a := reg .n) (b := reg (.lf (.k .cnt)))
    (t₁ := reg (.sc 1)) (t₂ := reg (.sc 2))
    (nodup_map_reg (l := [.n, .lf (.k .cnt), .sc 1, .sc 2]) (by simp)) v₆ { S with R := R₆ }
    (by dsimp only; rw [h6x (.sc 1) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 1)
    (by dsimp only; rw [h6x (.sc 2) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 2)
  obtain ⟨R₇, he₇, h7b, h7o⟩ := exec_upd body (S := S) (R := R₆) he₇
  dsimp only at h7b hm₇
  have h7f : ∀ k, k ≠ reg (.sc 0) → k ≠ reg (.lf (.k .mask)) → k ≠ reg (.lf .kr) →
      k ≠ reg (.lf .ur) → k ≠ reg (.lf (.k .cnt)) → R₇ k = S.R k := fun k h1 h2 h3 h4 h5 =>
    (h7o k h5).trans (h6f k h1 h2 h3 h4 h5)
  have hn6 : (R₆ (reg .n)).length = n := by
    rw [h6x .n (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hpar .n
  have h6c : (R₆ (reg (.lf (.k .cnt)))).length = R₀ := by
    rw [h6b, List.length_append, List.length_replicate, h5o (reg .rows) (reg_ne (by simp)),
      h4o (reg .rows) (reg_ne (by simp)), h3f (reg .rows) (reg_ne (by simp)) (reg_ne (by simp)),
      hpar .rows, h5o (reg (.lf (.k .cnt))) (reg_ne (by simp)),
      h4o (reg (.lf (.k .cnt))) (reg_ne (by simp)),
      h3f (reg (.lf (.k .cnt))) (reg_ne (by simp)) (reg_ne (by simp)), hrest (.lf (.k .cnt))]
    rfl
  have h7c : (R₇ (reg (.lf (.k .cnt)))).length = R₀ * 2 ^ n := by
    rw [h7b, length_flatMap_replicate, hn6, h6c, Nat.mul_comm]
  have h7m : R₇ (reg (.lf (.k .mask))) = binSyms n (2 ^ (ρ + a₀)) := by
    rw [h7o _ (reg_ne (by simp)), h6o _ (reg_ne (by simp)), h5o _ (reg_ne (by simp)),
      h4o _ (reg_ne (by simp)), h3m]
  have h7k : (R₇ (reg (.lf .kr))).length = K := by
    rw [h7o _ (reg_ne (by simp)), h6o _ (reg_ne (by simp)), h5o _ (reg_ne (by simp)), h4b,
      List.length_append, List.length_replicate, h3f (reg .K) (reg_ne (by simp)) (reg_ne (by simp)),
      h3f (reg (.lf .kr)) (reg_ne (by simp)) (reg_ne (by simp)), hpar .K, hrest (.lf .kr)]
    rfl
  have h7u : (R₇ (reg (.lf .ur))).length = u := by
    rw [h7o _ (reg_ne (by simp)), h6o _ (reg_ne (by simp)), h5b, List.length_append,
      List.length_replicate, h4o (reg .u) (reg_ne (by simp)), h4o (reg (.lf .ur)) (reg_ne
          (by simp)),
      h3f (reg .u) (reg_ne (by simp)) (reg_ne (by simp)),
      h3f (reg (.lf .ur)) (reg_ne (by simp)) (reg_ne (by simp)), hpar .u, hrest (.lf .ur)]
    rfl
  -- the kernel passes
  have hfit' : 0 < u → (ρ + a₀) + K * (0 + u - 1) < n := fun hu => by
    have := hfit (u - 1) (by omega)
    rw [Nat.zero_add]; omega
  have hlf : ∀ x : IntegerMultBounds.MathlibTM2.Node.LReg, x ≠ .k .arr → x ≠ .k .mask → x ≠ .kr → x ≠ .ur →
      x ≠ .k .cnt → R₇ (leafReg x) = S.R (reg (.lf x)) := fun x h0 h1 h2 h3 h4 => by
    rw [leafReg_of_ne h0]
    exact h7f _ (reg_ne (by simp)) (reg_ne (by simpa using h1)) (reg_ne (by simpa using h2))
      (reg_ne (by simpa using h3)) (reg_ne (by simpa using h4))
  obtain ⟨v₈, m₈, hu₈, hm₈, he₈⟩ := leafProg_exec body (lreg := leafReg) leafReg_injective hA
    hr hw (u := u) (K := K) (ρ := ρ + a₀) (c₀ := 0) hfit' Z v₇ { S with R := R₇ }
    { cf := by
        dsimp only; rw [hlf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hrest (.lf (.k .cf))
      rctr := by
        dsimp only; rw [hlf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hrest (.lf (.k .rctr))
      wctr := by
        dsimp only; rw [hlf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hrest (.lf (.k .wctr))
      cnt := by
        dsimp only; rw [leafReg_of_ne (by decide)]; exact h7c
      empty := fun x hx => by
        dsimp only
        have h := hrest (.lf (.k x))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [hlf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact h }
    (by dsimp only; rw [leafReg_arr, h7f _ (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]; exact hio)
    (by dsimp only; rw [leafReg_of_ne (by decide), h7m]; simp)
    (by dsimp only; rw [leafReg_of_ne (by decide)]; exact h7k)
    (by dsimp only; rw [leafReg_of_ne (by decide)]; exact h7u)
    (by dsimp only; rw [hlf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hrest (.lf .ut))
  dsimp only at he₈
  rw [leafReg_of_ne (by decide), leafReg_arr] at he₈
  set Y := encZ A w (k2l ((List.finRange u).map fun i : Fin u =>
    (⟨ρ + a₀ + K * (0 + i), leaf_lt hfit' i.2⟩ : Fin n)) Z) with hY
  set R₈ := Function.update (Function.update R₇ (reg (.lf (.k .mask)))
    (binSyms n (2 ^ (ρ + a₀ + K * (0 + (u - 1)))))) (reg .io) Y with hR₈
  -- clearing
  obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body (reg (.lf (.k .mask))) v₈ { S with R := R₈ }
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := uclear_exec body (reg (.lf .kr)) v₉
    { S with R := Function.update R₈ (reg (.lf (.k .mask))) [] }
  obtain ⟨v₁₁, hu₁₁, he₁₁⟩ := uclear_exec body (reg (.lf .ur)) v₁₀
    { S with R := Function.update (Function.update R₈ (reg (.lf (.k .mask))) []) (reg
        (.lf .kr)) [] }
  obtain ⟨v₁₂, hu₁₂, he₁₂⟩ := uclear_exec body (reg (.lf (.k .cnt))) v₁₁
    { S with R := Function.update (Function.update (Function.update R₈ (reg (.lf (.k .mask))) [])
      (reg (.lf .kr)) []) (reg (.lf .ur)) [] }
  obtain ⟨v₁₃, hu₁₃, he₁₃⟩ := uclear_exec body (reg (.sc 0)) v₁₂
    { S with R := Function.update (Function.update (Function.update (Function.update R₈
      (reg (.lf (.k .mask))) []) (reg (.lf .kr)) []) (reg (.lf .ur)) []) (reg (.lf (.k .cnt))) [] }
  have hkk : (List.finRange u).map (fun i : Fin u =>
      (⟨ρ + a₀ + K * (0 + i), leaf_lt hfit' i.2⟩ : Fin n)) =
      (List.finRange u).map (actMap a₀ ρ K u n hfit) :=
    List.map_congr_left fun i _ => Fin.ext (by simp only [actMap]; ring)
  refine ⟨v₁₃, _, by rw [hu₁₃, hu₁₂, hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆
      (Exec.seq he₇ (Exec.seq he₈ (Exec.seq he₉ (Exec.seq he₁₀ (Exec.seq he₁₁ (Exec.seq he₁₂
        he₁₃)))))))))))) rfl ?_⟩
  · have e2 : (R₁ (reg .ρ)).length = ρ := by
      rw [h1o (reg .ρ) (reg_ne (by simp))]; exact hpar .ρ
    have e4 : (R₃ (reg .K)).length = K := by
      rw [h3f (reg .K) (reg_ne (by simp)) (reg_ne (by simp))]; exact hpar .K
    have e5 : (R₄ (reg .u)).length = u := by
      rw [h4o (reg .u) (reg_ne (by simp)), h3f (reg .u) (reg_ne (by simp)) (reg_ne (by simp))]
      exact hpar .u
    have e6 : (R₅ (reg .rows)).length = R₀ := by
      rw [h5o (reg .rows) (reg_ne (by simp)), h4o (reg .rows) (reg_ne (by simp)),
        h3f (reg .rows) (reg_ne (by simp)) (reg_ne (by simp))]
      exact hpar .rows
    have e7 : m₇ ≤ 4 * (2 ^ n * R₀) + 9 * n + 4 := by rw [hn6, h6c] at hm₇; exact hm₇
    have e7s : (R₇ (reg (.sc 0))).length = ρ + a₀ := by
      rw [h7o _ (reg_ne (by simp)), h6o _ (reg_ne (by simp)), h5o _ (reg_ne (by simp)),
        h4o _ (reg_ne (by simp)), h3o _ (reg_ne (by simp)), h2s]
    have hcomm : R₀ * 2 ^ n = 2 ^ n * R₀ := Nat.mul_comm _ _
    dsimp only
    rw [hpar .a₀, e2, e4, e5, e6]
    simp only [hR₈]
    fupd
    rw [h7k, h7u, h7c, e7s, length_binSyms]
    unfold leafCost
    omega
  · congr 2
    funext k
    by_cases h0 : k = reg .io
    · subst h0
      simp only [hR₈]; fupd
      rw [hY, k2l_eq_k2s, hkk]
    by_cases h1 : k = reg (.lf (.k .mask))
    · subst h1; simp only [hR₈]; fupd; exact (hrest (.lf (.k .mask))).symm
    by_cases h2 : k = reg (.lf .kr)
    · subst h2; simp only [hR₈]; fupd; exact (hrest (.lf .kr)).symm
    by_cases h3 : k = reg (.lf .ur)
    · subst h3; simp only [hR₈]; fupd; exact (hrest (.lf .ur)).symm
    by_cases h4 : k = reg (.lf (.k .cnt))
    · subst h4; simp only [hR₈]; fupd; exact (hrest (.lf (.k .cnt))).symm
    by_cases h5 : k = reg (.sc 0)
    · subst h5; simp only [hR₈]; fupd; exact (hs 0).symm
    simp only [hR₈, Function.update_apply, h0, h1, h2, h3, h4, h5, ↓reduceIte]
    exact h7f k h5 h1 h2 h3 h4

end Leaf

/-! ### The layer procedure -/

section Layer

variable {Q Ka : ℕ} {U : Type}

/-- The procedures of the layer machine. -/
inductive LProc
  /-- The layer procedure. -/
  | layer

/-- **The body of the layer procedure**: peek `lev`; the leaf when `lev` is empty, the node
otherwise, with the factor programs calling the layer procedure for the child. -/
noncomputable def layerBody (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) : Pr LProc (nT CReg) Q (prime + Ka) U :=
  .seq (.act (peekR (reg .lev)))
    (.cond (fun v => !v.flag) leafP (nodeBody ds (factorProg hQ (.call .layer) ds)))

/-- The procedure table of the layer machine. -/
noncomputable def layerTable (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) : LProc → Pr LProc (nT CReg) Q (prime + Ka) U :=
  fun _ => layerBody hQ ds

/-- The pivot of a factor direction, `0` without a pivot. -/
noncomputable def pivotOf (vv : BinaryWalsh.Address m) : ℕ :=
  if h : ∃ i, vv i = 1 then (Fin.find _ h : ℕ) else 0

/-- The largest value of `f fw g` over the factor instructions `(fw, g)` of `program ds`. -/
noncomputable def facMax (ds : ComplexFramedExecution.Directions)
    (f : NWire → ZMod 4 × BinaryWalsh.Address m → ℕ) : ℕ :=
  ((program ds).map fun i => match i with
    | .factor fw g => f fw g
    | .gate _ => 0).foldr max 0

lemma le_facMax (ds : ComplexFramedExecution.Directions)
    (f : NWire → ZMod 4 × BinaryWalsh.Address m → ℕ) {fw : NWire}
    {g : ZMod 4 × BinaryWalsh.Address m} (h : Instr.factor fw g ∈ program ds) :
    f fw g ≤ facMax ds f := by
  unfold facMax
  generalize program ds = l at h ⊢
  induction l with
  | nil => simp at h
  | cons i l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · simp only [List.map_cons, List.foldr_cons]
        exact le_max_of_le_right (ih h)

/-- **The step bound of the layer procedure** at level `j` with offset `a₀`, `T` host registers:
the leaf at level `0`; at level `j + 1` the node (`nodeCost`) with the factor bound `facMax` of
`factorCost`, each factor with the bound of the call of its child at level `j`, offset
`a₀ + s · K · bits u j` for the pivot `s`; plus the call, the peek and the dispatch. -/
noncomputable def layerCost (A T : ℕ) (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n r w Gd : ℕ) : ℕ → ℕ → ℕ
  | 0, a₀ => leafCost u K ρ a₀ R₀ n r w + 4
  | j + 1, a₀ => nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w
      (facMax ds fun _ g => factorCost A T ds j u K ρ a₀ R₀ n r w Gd g
        (layerCost A T ds u K ρ R₀ n r w Gd j (a₀ + pivotOf g.2 * (K * bits u j)))) + 4

/-- The leaf bits grow with the level. -/
lemma bits_le_succ (u j : ℕ) : bits u j ≤ bits u (j + 1) := by
  show bits u j ≤ m * bits u j
  exact Nat.le_mul_of_pos_left _ (by norm_num [m])

lemma le_bits (u : ℕ) : ∀ j, u ≤ bits u j
  | 0 => le_rfl
  | j + 1 => (le_bits u j).trans (bits_le_succ u j)

/-- **The layer procedure.** From the parameters of level `j` (`L = K · bits u j`,
`rows = rowsAt R₀ j`, `rw = r w`), every register at rest (the `bc` registers empty), every left
stack empty and `io` holding the stream of `Z`, the call of the layer procedure ends with `io`
holding the stream of `layerZ u ds R₀ j e Z`, `e i = a₀ + ρ + K i`, every other register and `user`
as before, within `layerCost (nT CReg) ds u K ρ R₀ n r w j a₀` steps. Hypotheses: the alphabet
covers the slot XORs (`14 ≤ A`), the leaf (`9 ^ 4 ≤ A + 4`), the row roles (`NW ≤ A + 4`) and the
gate automata; `ρ < K`; the active bits fit (`a₀ + K · bits u j ≤ n`); the child exponents fit the
word (`expZ u ds i ≤ w`, `i < j`); `1 ≤ u, r, w, R₀`. -/
theorem layer_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {u K ρ R₀ n r w Gd : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀) :
    ∀ (j : ℕ), (∀ i < j, expZ u ds i ≤ w) →
    ∀ (a₀ : ℕ) (hfit : ∀ i < bits u j, a₀ + ρ + K * i < n), a₀ + K * bits u j ≤ n →
      (1 ≤ j → 2 ≤ bits u (j - 1) → 1 ≤ Gd ∧ Gd + 3 ≤ K ∧ (bits u (j - 1) - 1) * Gd ≤ a₀ ∧
        a₀ + K * bits u j + 3 * ((bits u (j - 1) - 1) * Gd) ≤ n) →
    ∀ (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT CReg) Q (prime + Ka) U)
      (S : Stacks (nT CReg) (prime + Ka)), (∀ y, S.L y = []) →
      ParState S.R j u K ρ a₀ (K * bits u j) (rowsAt R₀ j) n w (r * w) →
      Rest (bcRestC Gd) n r w S.R → S.R (reg .io) = encZ (prime + Ka) w Z →
      ∃ (v' : HS (nT CReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
        c ≤ layerCost (prime + Ka) (nT CReg) ds u K ρ R₀ n r w Gd j a₀ ∧
        Exec (layerTable hQ ds) (.call .layer) (mk v S) c (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ (prime + Ka) w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) n hfit) Z)) }) := by
  intro j
  induction j with
  | zero =>
      intro _ a₀ hfit _ _ Z v S _ hpar hrest hio
      have hlev : S.R (reg .lev) = [] := List.eq_nil_of_length_eq_zero (hpar .lev)
      have hp := Exec.act (body := layerTable (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := leafP_exec (layerTable hQ ds) hA9 hr hw hfit Z
        { v with flag := (S.R (reg .lev)).head?.isSome } S hpar hrest hio
      have hc₁' : c₁ ≤ leafCost u K ρ a₀ R₀ n r w := hc₁
      refine ⟨v₁, 1 + (c₁ + 1) + 2, hu₁, ?_, ?_⟩
      · simp only [layerCost]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_true (by simp [hlev]) he₁))
  | succ j ih =>
      intro hTw a₀ hfit hfitL hres Z v S hL hpar hrest hio
      have hL₁ : K * bits u (j + 1) = m * (K * bits u j) := by
        rw [show bits u (j + 1) = m * bits u j from rfl]; ring
      have hres' : 2 ≤ bits u j → 1 ≤ Gd ∧ Gd + 3 ≤ K ∧ (bits u j - 1) * Gd ≤ a₀ ∧
          a₀ + m * (K * bits u j) + 3 * ((bits u j - 1) * Gd) ≤ n := by
        intro hk2
        have := hres (by omega) (by simpa using hk2)
        simp only [Nat.add_sub_cancel] at this
        rw [← hL₁]; exact this
      have hlev : (S.R (reg .lev)).length = j + 1 := hpar .lev
      obtain ⟨x₀, rest, hl⟩ : ∃ x₀ rest, S.R (reg .lev) = x₀ :: rest := by
        cases h : S.R (reg .lev) with
        | nil => rw [h] at hlev; simp at hlev
        | cons x rest => exact ⟨x, rest, rfl⟩
      have hp := Exec.act (body := layerTable (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      set cf := facMax ds fun _ g => factorCost (prime + Ka) (nT CReg) ds j u K ρ a₀ R₀ n r w Gd g
        (layerCost (prime + Ka) (nT CReg) ds u K ρ R₀ n r w Gd j (a₀ + pivotOf g.2 * (K * bits u j)))
        with hcf
      have hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
          FactorSpecL (layerTable (Ka := Ka) (U := U) hQ ds)
            (factorProg (Ka := Ka) (U := U) hQ (.call .layer) ds fw g) (bcRestC Gd) j u K ρ a₀
            (K * bits u (j + 1)) (rowsAt R₀ (j + 1)) n r w (k := bits u j)
            (actMap a₀ ρ K (bits u (j + 1)) n hfit)
            (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
            (expZ u ds j) fw g cf := by
        intro fw g hg
        refine (factorProg_spec (layerTable hQ ds) hQ (.call .layer) ds hA hr hw hρ hu hR₀ hfit
          hfitL (hTw j (by omega)) hres' fw g _ ?_).mono (le_facMax ds
            (fun _ g => factorCost (prime + Ka) (nT CReg) ds j u K ρ a₀ R₀ n r w Gd g
              (layerCost (prime + Ka) (nT CReg) ds u K ρ R₀ n r w Gd j
                (a₀ + pivotOf g.2 * (K * bits u j)))) hg)
        intro hs hfit'
        have hpv : pivotOf g.2 = (Fin.find _ hs : ℕ) := by simp [pivotOf, hs]
        rw [hpv]
        have hsm : (Fin.find _ hs : ℕ) + 1 ≤ m := (Fin.find _ hs).2
        have hfitL' : a₀ + (Fin.find _ hs : ℕ) * (K * bits u j) + K * bits u j ≤ n := by
          have h1 : ((Fin.find _ hs : ℕ) + 1) * (K * bits u j) ≤ m * (K * bits u j) :=
            Nat.mul_le_mul_right _ hsm
          have h2 : K * bits u (j + 1) = m * (K * bits u j) := by
            rw [show bits u (j + 1) = m * bits u j from rfl]; ring
          have h3 : ((Fin.find _ hs : ℕ) + 1) * (K * bits u j) =
              (Fin.find _ hs : ℕ) * (K * bits u j) + K * bits u j := by ring
          omega
        have hres'' : 1 ≤ j → 2 ≤ bits u (j - 1) → 1 ≤ Gd ∧ Gd + 3 ≤ K ∧
            (bits u (j - 1) - 1) * Gd ≤ a₀ + (Fin.find _ hs : ℕ) * (K * bits u j) ∧
            a₀ + (Fin.find _ hs : ℕ) * (K * bits u j) + K * bits u j +
              3 * ((bits u (j - 1) - 1) * Gd) ≤ n := by
          intro hj hk2'
          have hbl : bits u (j - 1) ≤ bits u j := by
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            simpa using bits_le_succ u j'
          obtain ⟨hGd, hGK, hfront, hback⟩ := hres' (by omega)
          have h1 : (bits u (j - 1) - 1) * Gd ≤ (bits u j - 1) * Gd :=
            Nat.mul_le_mul_right _ (by omega)
          refine ⟨hGd, hGK, by omega, ?_⟩
          have h2 : ((Fin.find _ hs : ℕ) + 1) * (K * bits u j) ≤ m * (K * bits u j) :=
            Nat.mul_le_mul_right _ hsm
          have h3 : ((Fin.find _ hs : ℕ) + 1) * (K * bits u j) =
              (Fin.find _ hs : ℕ) * (K * bits u j) + K * bits u j := by ring
          omega
        intro Z' v' S' hL' hpar' hrest' hio'
        exact ih (fun i hi => hTw i (by omega)) _ hfit' hfitL' hres'' Z' v' S' hL' hpar' hrest'
          hio'
      obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := nodeBody_execL_layerZ (layerTable hQ ds) ds
        (factorProg hQ (.call .layer) ds) (by omega) hNW hgate hr hw (by omega) hfit hfac Z
        { v with flag := (S.R (reg .lev)).head?.isSome } S hL hpar hrest hio
      refine ⟨v₁, 1 + (c₁ + 1) + 2, hu₁, ?_, ?_⟩
      · simp only [layerCost]; rw [← hcf]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_false (by simp [hl]) he₁))

/-- `layer_exec` as the specification `CallSpec` of the call of the layer procedure. -/
theorem layer_callSpec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {u K ρ R₀ n r w Gd : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (j : ℕ) (hTw : ∀ i < j, expZ u ds i ≤ w) (a₀ : ℕ) (hfit : ∀ i < bits u j, a₀ + ρ + K * i < n)
    (hfitL : a₀ + K * bits u j ≤ n)
    (hres : 1 ≤ j → 2 ≤ bits u (j - 1) → 1 ≤ Gd ∧ Gd + 3 ≤ K ∧ (bits u (j - 1) - 1) * Gd ≤ a₀ ∧
      a₀ + K * bits u j + 3 * ((bits u (j - 1) - 1) * Gd) ≤ n) :
    CallSpec (layerTable (Ka := Ka) (U := U) hQ ds) (.call .layer) (bcRestC Gd) ds R₀ j u K ρ a₀
      (K * bits u j) n r w hfit (layerCost (prime + Ka) (nT CReg) ds u K ρ R₀ n r w Gd j a₀) :=
  fun Z v S hL hpar hrest hio =>
    layer_exec hQ ds hA hA9 hNW hgate hr hw hρ hu hR₀ j hTw a₀ hfit hfitL hres Z v S hL
      hpar hrest hio

end Layer

end IntegerMultBounds.MathlibTM2.LayerMachine
