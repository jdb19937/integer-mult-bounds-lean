module

public import IntegerMultBounds.MathlibTM2.Node.Phase
public import IntegerMultBounds.MathlibTM2.Node.Leaf
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# The register file of the layer machine

One inductive `LReg BReg` names every register of the layer machine; it is parametric in the
registers `BReg` of the basis-change passes. `LReg BReg` is finite with decidable equality, and
`regEquiv : LReg BReg ≃ Fin (nT BReg)` numbers the registers, `nT BReg = card (LReg BReg)`. The
register map `reg` is injective (`reg_injective`, `reg_inj`, `reg_ne`), so two registers named by
distinct constructors are distinct host registers.

**Registers.**
* `io`: the array of the current call (`encZ A w Z`).
* `wire v`, `wtmp v` (`v : NWire`): the bank of the node and its temporaries (`Node/Gate.lean`'s
  `ρ`, `σ`).
* `park`: LIFO parking of the parent's wires during a child call.
* `ctr tmp cS cR tS tR`: the word counter, its spare and the shift registers of `gateProg`;
  `ctr` and `tmp` also serve the one-wire Gaussian automata.
* `ph x` (`x : PhaseReg`): the registers of `phaseProg`. The array role is played by the target
  wire (`phMap`), so `ph .arr` is never used.
* `lf x` (`x : Node.LReg`): the registers of the leaf (`leafProg`); the array role `lf (.k .arr)`
  is never used (the leaf runs on `io`).
* `rowctr rowtmp rctmp racc lenctr`: routing by rows. `rowctr` holds the row length `2^n r w`,
  `rowtmp` is its spare, `rctmp` the spare of the row count in a merge, `racc` the merge
  accumulator, `lenctr` a length counter for counted moves.
* parameters (unary): `lev` (level), `u` (leaf bits), `K` (bit stride), `ρ` and `a₀` (the active
  bit `i` is at `a₀ + ρ + K i`), `L` (slot width), `rows` (row count), `n` (address bits), `w`
  (word length), `rw` (`r w`), `Tc` (the child exponent while a node runs, empty at rest).
* `sc i` (`i : Fin 6`): scratch registers of the unary utilities (`Node/Params.lean`).
* `bc x` (`x : BReg`): the basis-change registers.
* `st`, `cs`: scan-slot indices (automaton state, block counter); they never hold data.

**Rest states.** `restSpec bcRest n r w x l` is the rest state of register `x` with contents `l`:
wires, temporaries, spares, `Tc` and scratch empty; `ctr` holds `w` symbols, `cS` one and `cR`
`w - 1`; the record counters `ph .rc`, `lf (.k .rctr)` hold `r w` symbols, the word counters
`ph .wc`, `lf (.k .wctr)` hold `w`, the address fields `ph .af`, `lf (.k .cf)` are `binSyms n 0`,
and the other phase and leaf registers (record counts and masks included) are empty; `rowctr`
holds `2^n r w` symbols; `bc x` satisfies `bcRest x`; `io`, `park`, the parameters, the scan
slots and the unused array roles are unconstrained. `Rest bcRest n r w Rg`: every register is at
rest; `RestBut … ex Rg`: every register outside `ex` is at rest. `RestBut.congr`,
`Rest.restBut_of_frame`: these predicates only read the registers they constrain;
`Rest.update_io`, `ParState.update_io`: both survive a change of `io`.

**Parameters.** `ParState Rg j u K ρ a₀ L rows n w rw`: the parameter registers `parRegs` hold
these unary lengths (`parSpec`); `ParState.congr` transfers it along agreement on `parRegs`.

**Node-internal state.** `NodeRegs bcRest Rg j u K ρ a₀ L rows n r w Tc`: the state of the node
body at level `j + 1` between two instructions: the parameters of level `j + 1` (with `rw = r w`),
every register other than the wires and `Tc` at rest, `io` empty and `Tc` holding `Tc` symbols;
`NodeRegs.congr`: it does not read the wires.

**Factor programs.** `FactorSpec body prog bcRest … e child Tc fw g cf`: from the node-internal
state with every wire `x` holding `encZ A w (B x)`, `prog` ends with every wire `x` holding
`encZ A w (execM e child Tc (.factor fw g) B x)`, every other register and `user` as before,
within `cf` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg

deriving instance Fintype for PhaseReg

instance : Fintype KReg :=
  Fintype.ofList [.arr, .mask, .cf, .tm0, .tm1, .rctr, .wctr, .tmp, .cnt, .ctmp, .r0, .r1, .e0, .e1,
    .o0, .o1] (by intro x; cases x <;> simp)

deriving instance Fintype for IntegerMultBounds.MathlibTM2.Node.LReg

/-- The registers of the layer machine, with basis-change registers `BReg`. -/
inductive LReg (BReg : Type) where
  /-- The array of the current call. -/
  | io
  /-- The bank of the node: one register per wire. -/
  | wire (v : NWire)
  /-- The temporaries of the bank. -/
  | wtmp (v : NWire)
  /-- LIFO parking of the parent's wires during a child call. -/
  | park
  /-- The word counter of the gate automata (`w` symbols at rest). -/
  | ctr
  /-- The spare of the gate automata. -/
  | tmp
  /-- The shift counter (one symbol at rest). -/
  | cS
  /-- The shift counter (`w - 1` symbols at rest). -/
  | cR
  /-- A spare of the shifts. -/
  | tS
  /-- A spare of the shifts. -/
  | tR
  /-- The phase registers (`ph .arr` is never used). -/
  | ph (x : PhaseReg)
  /-- The leaf registers (`lf (.k .arr)` is never used). -/
  | lf (x : IntegerMultBounds.MathlibTM2.Node.LReg)
  /-- The row length counter (`2^n r w` symbols at rest). -/
  | rowctr
  /-- The spare of `rowctr`. -/
  | rowtmp
  /-- The spare of the row count in a merge. -/
  | rctmp
  /-- The merge accumulator. -/
  | racc
  /-- A length counter for counted moves. -/
  | lenctr
  /-- The level `j`. -/
  | lev
  /-- The number of leaf bits `u`. -/
  | u
  /-- The bit stride `K`. -/
  | K
  /-- The bit offset `ρ`. -/
  | ρ
  /-- The bit offset `a₀`. -/
  | a₀
  /-- The slot width `L`. -/
  | L
  /-- The row count. -/
  | rows
  /-- The address width `n`. -/
  | n
  /-- The word length `w`. -/
  | w
  /-- The record length `r w`. -/
  | rw
  /-- The child exponent while a node runs. -/
  | Tc
  /-- Scratch registers of the unary utilities. -/
  | sc (i : Fin 6)
  /-- The basis-change registers. -/
  | bc (x : BReg)
  /-- Scan slot of the automaton states. -/
  | st
  /-- Scan slot of the block counters. -/
  | cs
  deriving DecidableEq

section Instances

variable {BReg : Type} [Fintype BReg]

set_option synthInstance.maxSize 2048 in
deriving instance Fintype for LReg

end Instances

variable (BReg : Type) [Fintype BReg]

/-- The number of host registers. -/
abbrev nT : ℕ := Fintype.card (LReg BReg)

/-- The numbering of the registers. -/
noncomputable def regEquiv : LReg BReg ≃ Fin (nT BReg) := Fintype.equivFin _

variable {BReg}

/-- The host register of a register name. -/
noncomputable def reg (x : LReg BReg) : Fin (nT BReg) := regEquiv BReg x

lemma reg_injective : Function.Injective (reg (BReg := BReg)) := (regEquiv BReg).injective

@[simp] lemma reg_inj {x y : LReg BReg} : reg x = reg y ↔ x = y := reg_injective.eq_iff

lemma reg_ne {x y : LReg BReg} (h : x ≠ y) : reg x ≠ reg y := reg_injective.ne h

lemma nodup_map_reg {l : List (LReg BReg)} (h : l.Nodup) : (l.map reg).Nodup :=
  h.map reg_injective

/-- The phase registers with the array role played by `tgt`. -/
noncomputable def phMap (tgt : Fin (nT BReg)) (x : PhaseReg) : Fin (nT BReg) :=
  if x = .arr then tgt else reg (.ph x)

lemma phMap_injective {tgt : Fin (nT BReg)} (h : ∀ x, tgt ≠ reg (.ph x)) :
    Function.Injective (phMap tgt) := by
  intro x y hxy
  unfold phMap at hxy
  by_cases hx : x = .arr <;> by_cases hy : y = .arr
  · rw [hx, hy]
  · simp only [hx, hy, ↓reduceIte] at hxy; exact absurd hxy (h y)
  · simp only [hx, hy, ↓reduceIte] at hxy; exact absurd hxy.symm (h x)
  · simp only [hx, hy, ↓reduceIte, reg_inj, LReg.ph.injEq] at hxy; exact hxy

@[simp] lemma phMap_arr (tgt : Fin (nT BReg)) : phMap tgt .arr = tgt := by simp [phMap]

lemma phMap_of_ne (tgt : Fin (nT BReg)) {x : PhaseReg} (hx : x ≠ .arr) :
    phMap tgt x = reg (.ph x) := by simp [phMap, hx]

/-! ### Rest states and parameters -/

section Specs

variable {A : ℕ}

/-- The rest state of a phase register: `rc` holds `r w` symbols, `wc` holds `w`, `af` is the
address field `binSyms n 0`; `arr` is unconstrained (never used); the others are empty. -/
def phRest (n r w : ℕ) : PhaseReg → List (Fin (A + 4)) → Prop
  | .arr, _ => True
  | .rc, l => l.length = r * w
  | .wc, l => l.length = w
  | .af, l => l = binSyms n 0
  | _, l => l = []

/-- The rest state of a leaf register: `rctr` holds `r w` symbols, `wctr` holds `w`, `cf` is the
address field `binSyms n 0`; the array role is unconstrained (never used); the others are
empty. -/
def lfRest (n r w : ℕ) : IntegerMultBounds.MathlibTM2.Node.LReg → List (Fin (A + 4)) → Prop
  | .k .arr, _ => True
  | .k .rctr, l => l.length = r * w
  | .k .wctr, l => l.length = w
  | .k .cf, l => l = binSyms n 0
  | _, l => l = []

/-- The rest state of a register. -/
def restSpec (bcRest : BReg → List (Fin (A + 4)) → Prop) (n r w : ℕ) :
    LReg BReg → List (Fin (A + 4)) → Prop
  | .wire _, l => l = []
  | .wtmp _, l => l = []
  | .ctr, l => l.length = w
  | .tmp, l => l = []
  | .cS, l => l.length = 1
  | .cR, l => l.length = w - 1
  | .tS, l => l = []
  | .tR, l => l = []
  | .ph x, l => phRest n r w x l
  | .lf x, l => lfRest n r w x l
  | .rowctr, l => l.length = 2 ^ n * r * w
  | .rowtmp, l => l = []
  | .rctmp, l => l = []
  | .racc, l => l = []
  | .lenctr, l => l = []
  | .Tc, l => l = []
  | .sc _, l => l = []
  | .bc x, l => bcRest x l
  | _, _ => True

/-- Every register outside `ex` is at rest. -/
def RestBut (bcRest : BReg → List (Fin (A + 4)) → Prop) (n r w : ℕ) (ex : LReg BReg → Prop)
    (Rg : Fin (nT BReg) → List (Fin (A + 4))) : Prop :=
  ∀ x, ¬ ex x → restSpec bcRest n r w x (Rg (reg x))

/-- Every register is at rest. -/
def Rest (bcRest : BReg → List (Fin (A + 4)) → Prop) (n r w : ℕ)
    (Rg : Fin (nT BReg) → List (Fin (A + 4))) : Prop :=
  ∀ x, restSpec bcRest n r w x (Rg (reg x))

variable {bcRest : BReg → List (Fin (A + 4)) → Prop} {n r w : ℕ}
  {Rg Rg' : Fin (nT BReg) → List (Fin (A + 4))}

lemma Rest.restBut (h : Rest bcRest n r w Rg) (ex : LReg BReg → Prop) :
    RestBut bcRest n r w ex Rg := fun x _ => h x

lemma RestBut.mono {ex ex' : LReg BReg → Prop} (h : RestBut bcRest n r w ex Rg)
    (hex : ∀ x, ex x → ex' x) : RestBut bcRest n r w ex' Rg :=
  fun x hx => h x (fun h' => hx (hex x h'))

/-- `RestBut` only reads the registers outside `ex`. -/
lemma RestBut.congr {ex : LReg BReg → Prop} (h : RestBut bcRest n r w ex Rg)
    (hR : ∀ x, ¬ ex x → Rg' (reg x) = Rg (reg x)) : RestBut bcRest n r w ex Rg' :=
  fun x hx => by rw [hR x hx]; exact h x hx

/-- Registers in `ex` at rest complete `RestBut` to `Rest`. -/
lemma RestBut.rest {ex : LReg BReg → Prop} (h : RestBut bcRest n r w ex Rg)
    (hex : ∀ x, ex x → restSpec bcRest n r w x (Rg (reg x))) : Rest bcRest n r w Rg := by
  intro x
  by_cases hx : ex x
  · exact hex x hx
  · exact h x hx

/-- The parameter registers. -/
def parRegs : List (LReg BReg) := [.lev, .u, .K, .ρ, .a₀, .L, .rows, .n, .w, .rw]

/-- The unary value of each parameter register. -/
def parSpec (j u K ρ a₀ L rows n w rw : ℕ) : LReg BReg → List (Fin (A + 4)) → Prop
  | .lev, l => l.length = j
  | .u, l => l.length = u
  | .K, l => l.length = K
  | .ρ, l => l.length = ρ
  | .a₀, l => l.length = a₀
  | .L, l => l.length = L
  | .rows, l => l.length = rows
  | .n, l => l.length = n
  | .w, l => l.length = w
  | .rw, l => l.length = rw
  | _, _ => True

/-- The parameter registers hold `j, u, K, ρ, a₀, L, rows, n, w, rw` in unary. -/
def ParState (Rg : Fin (nT BReg) → List (Fin (A + 4))) (j u K ρ a₀ L rows n w rw : ℕ) : Prop :=
  ∀ x, parSpec j u K ρ a₀ L rows n w rw x (Rg (reg x))

/-- `ParState` only reads the parameter registers. -/
lemma ParState.congr {j u K ρ a₀ L rows n w rw : ℕ} (h : ParState Rg j u K ρ a₀ L rows n w rw)
    (hR : ∀ x ∈ parRegs (BReg := BReg), Rg' (reg x) = Rg (reg x)) :
    ParState Rg' j u K ρ a₀ L rows n w rw := by
  intro x
  cases x <;> first
    | exact trivial
    | (rw [hR _ (by simp [parRegs])]; exact h _)

/-- A frame outside a set of registers containing no parameter register keeps `ParState`. -/
lemma ParState.frame {j u K ρ a₀ L rows n w rw : ℕ} (h : ParState Rg j u K ρ a₀ L rows n w rw)
    (W : Fin (nT BReg) → Prop) (hW : ∀ x ∈ parRegs (BReg := BReg), ¬ W (reg x))
    (hR : ∀ k, ¬ W k → Rg' k = Rg k) : ParState Rg' j u K ρ a₀ L rows n w rw :=
  h.congr fun x hx => hR _ (hW x hx)

omit [Fintype BReg] in
/-- A parameter register is not `io`, a wire or `Tc`. -/
lemma parRegs_ne {x : LReg BReg} (hx : x ∈ parRegs (BReg := BReg)) :
    x ≠ .io ∧ (∀ y, x ≠ .wire y) ∧ x ≠ .Tc := by
  simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Registers outside `io` and `ex` keeping their contents keep `RestBut … ex` (`io` is
unconstrained at rest). -/
lemma Rest.restBut_of_frame (h : Rest bcRest n r w Rg) (ex : LReg BReg → Prop)
    (hR : ∀ x, x ≠ .io → ¬ ex x → Rg' (reg x) = Rg (reg x)) : RestBut bcRest n r w ex Rg' := by
  intro x hx
  by_cases hio : x = .io
  · subst hio; exact trivial
  · rw [hR x hio hx]; exact h x

/-- Changing `io` keeps `ParState`. -/
lemma ParState.update_io {j u K ρ a₀ L rows n w rw : ℕ} (h : ParState Rg j u K ρ a₀ L rows n w rw)
    (l : List (Fin (A + 4))) :
    ParState (Function.update Rg (reg .io) l) j u K ρ a₀ L rows n w rw :=
  h.congr fun _ hx => Function.update_of_ne (reg_ne (parRegs_ne hx).1) _ _

/-- Changing `io` keeps `Rest`. -/
lemma Rest.update_io (h : Rest bcRest n r w Rg) (l : List (Fin (A + 4))) :
    Rest bcRest n r w (Function.update Rg (reg .io) l) := by
  intro x
  by_cases hx : x = .io
  · subst hx; exact trivial
  · rw [Function.update_of_ne (reg_ne hx)]; exact h x

end Specs

/-! ### The node-internal state and factor programs -/

section Factor

variable {A : ℕ}

/-- The registers of the node body at level `j + 1` between two of its instructions: the
parameters of level `j + 1` (with `rw = r w`), every register other than the wires and `Tc` at
rest, `io` empty and `Tc` holding `Tc` symbols. -/
structure NodeRegs (bcRest : BReg → List (Fin (A + 4)) → Prop)
    (Rg : Fin (nT BReg) → List (Fin (A + 4))) (j u K ρ a₀ L rows n r w Tc : ℕ) : Prop where
  par : ParState Rg (j + 1) u K ρ a₀ L rows n w (r * w)
  rest : RestBut bcRest n r w (fun x => (∃ v, x = .wire v) ∨ x = .Tc) Rg
  io : Rg (reg .io) = []
  tc : (Rg (reg .Tc)).length = Tc

/-- `NodeRegs` does not read the wires. -/
lemma NodeRegs.congr {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {Rg Rg' : Fin (nT BReg) → List (Fin (A + 4))} {j u K ρ a₀ L rows n r w Tc : ℕ}
    (h : NodeRegs bcRest Rg j u K ρ a₀ L rows n r w Tc)
    (hR : ∀ k, (∀ v, k ≠ reg (.wire v)) → Rg' k = Rg k) :
    NodeRegs bcRest Rg' j u K ρ a₀ L rows n r w Tc where
  par := h.par.congr fun x hx => hR _ fun v => reg_ne (by
    simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  rest := h.rest.congr fun x hx => hR _ fun v e => hx (Or.inl ⟨v, reg_injective e⟩)
  io := (hR _ fun v => reg_ne (by simp)).trans h.io
  tc := by rw [hR _ fun v => reg_ne (by simp)]; exact h.tc

variable {T Q : ℕ} {U P : Type}

/-- **Factor programs.** `prog` implements the scaled factor `(fw, g)` of the node at level
`j + 1` on wire arrays with `R` rows of `r` coefficients, with active bits `e`, child semantics
`child` and child exponent `Tc`: from the node-internal state (`NodeRegs`) with every wire `x`
holding `encZ A w (B x)`, it ends with every wire `x` holding
`encZ A w (execM e child Tc (.factor fw g) B x)`, every other register and `user` as before,
within `cf` steps. -/
def FactorSpec (body : P → Pr P (nT BReg) Q A U) (prog : Pr P (nT BReg) Q A U)
    (bcRest : BReg → List (Fin (A + 4)) → Prop) (j u K ρ a₀ L rows n r w : ℕ) {R k : ℕ}
    (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n) (Tc : ℕ) (fw : NWire)
    (g : ZMod 4 × BinaryWalsh.Address m) (cf : ℕ) : Prop :=
  ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
    (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ cf ∧ Exec body prog (mk v S) c (mk v' { S with R := R' }) ∧
      (∀ x, R' (reg (.wire x)) = encZ A w (execM e child Tc (.factor fw g) B x)) ∧
      ∀ i, (∀ x, i ≠ reg (.wire x)) → R' i = S.R i

/-- **Exact instruction programs.** `prog` implements the translation, slot XOR or slot phase
`ins` of the node at level `j + 1`: from the node-internal state with every wire `x` holding
`encZ A w (B x)`, it ends with every wire `x` holding `encZ A w (execM e child Tc ins B x)`, every
other register and `user` as before, within `cm` steps. -/
def MonoSpec (body : P → Pr P (nT BReg) Q A U) (prog : Pr P (nT BReg) Q A U)
    (bcRest : BReg → List (Fin (A + 4)) → Prop) (j u K ρ a₀ L rows n r w : ℕ) {R k : ℕ}
    (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n) (Tc : ℕ) (ins : Instr)
    (cm : ℕ) : Prop :=
  ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
    (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ cm ∧ Exec body prog (mk v S) c (mk v' { S with R := R' }) ∧
      (∀ x, R' (reg (.wire x)) = encZ A w (execM e child Tc ins B x)) ∧
      ∀ i, (∀ x, i ≠ reg (.wire x)) → R' i = S.R i

end Factor

end IntegerMultBounds.MathlibTM2.LayerMachine
