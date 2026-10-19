module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Induction
public import IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound

/-! Full execution of the actual fixed root interchange program on power-widthSlot
binary arrays. Root descriptor/return-frame construction, recursive execution,
physical restoration, and genuine halt are all included. The complete bank is
restored except for the exact full H/D transpose of the sole I/O array. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (implementation widthSlot pcStack returnWidth returnCapacity)
open BaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k depth : ℕ}

omit [Net] in
/-- Canonical blank work tapes satisfy every allocation invariant automatically. -/
theorem blank_ready : Ready (fun _ => blank) 0 (SharedBank.empty 1 prime)
    (SharedBank.empty 1 prime) (SharedBank.empty 2 prime) :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- The actual graph started with its physically saved root sentinel reaches
its halt node with exact transposed data and all original caller tapes. -/
theorem graph_hoare (capacity : Fintype.card PC ≤ 2^k)
    (v : Descriptor) (shape : Depth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime (Control.program capacity widthSlot pcStack (implementation k))
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks hs st (rootCode capacity)))
        (tapeCount capacity widthSlot pcStack (implementation k)))
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        (tapeCount capacity widthSlot pcStack (implementation k)))
      (Budget.budget k depth (volume prime v)) := by
  intro ww hww
  subst ww
  obtain ⟨n,hn,htrace⟩ := Induction.run capacity depth .halt v shape hs hs hv
    (RecursiveRowsNode.header_length v shape.positive hs hv) f p node scalar st ready x
  exact ⟨n,_,hn,htrace,BaseExecution.halt_entry capacity _,rfl⟩

/-- All real root setup steps are charged before the same fixed recursive graph.
No assumed machine block, recursive trace or abstract interchange oracle remains. -/
theorem root_hoare (v : Descriptor) (shape : Depth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Implementation.program
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Root.tapeCount)
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Root.tapeCount)
      (BinaryDescriptorFrames.cost Implementation.rootFields (Root.words hs)+
        1+returnWidth+1+Budget.budget returnWidth depth (volume prime v)) :=
  Root.root_hoare (roles (RecursiveRowsSerialization.sourceData wires (encoded x)))
    hs f p node scalar st _ _ (graph_hoare returnCapacity v shape hs hv f p node scalar st ready x)

/-- Root setup and its joining transition add a fixed linear-volume charge. -/
def rootOverhead : ℕ := 74+returnWidth

def rootBudget (depth V : ℕ) : ℕ :=
  rootOverhead*V+Budget.budget returnWidth depth V

theorem root_budget_hoare (v : Descriptor) (shape : Depth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Implementation.program
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Root.tapeCount)
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Root.tapeCount)
      (rootBudget depth (volume prime v)) := by
  have hsetup := Root.setup_cost_linear v shape.positive hs hv
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
  apply (root_hoare v shape hs hv f p node scalar st ready x).consequence (fun _ h => h) (fun _ h => h)
  unfold rootBudget rootOverhead
  nlinarith

/-- A single constant for the single fixed compiled root program. -/
def constant : ℝ := rootOverhead+BudgetBound.constant returnWidth

theorem constant_positive : 0 < constant := by
  have h := BudgetBound.constant_positive returnWidth
  have hn : (0 : ℝ) ≤ rootOverhead := Nat.cast_nonneg _
  unfold constant
  linarith

theorem rootBudget_bound (depth V : ℕ) :
    (rootBudget depth V : ℝ) ≤ constant*(V : ℝ)*((width^depth : ℕ) : ℝ)^BudgetBound.tau := by
  have hbound := BudgetBound.power_width_bound returnWidth depth V
  have hw : (1 : ℝ) ≤ ((width^depth : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ width^depth from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by have := two_le_width; omega)))
  have hpow := Real.one_le_rpow hw (Net.net).tau_pos.le
  have hlin : (rootOverhead : ℝ)*V ≤ (rootOverhead : ℝ)*V*((width^depth : ℕ) : ℝ)^BudgetBound.tau := by
    nlinarith [show (0 : ℝ) ≤ (rootOverhead : ℝ)*V by positivity]
  simp only [rootBudget,Nat.cast_add,Nat.cast_mul,constant]
  nlinarith

/-- Actual execution of the one fixed root machine halts in the certified
sublinear-widthSlot exponent bound and restores every cell/head outside its output.
The shape premises are exactly the current power-widthSlot/divisible-row interface. -/
theorem halts_power_bound (v : Descriptor) (shape : Depth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    ∃ n : ℕ, ∃ c, (n : ℝ) ≤ constant*(volume prime v : ℝ)*(v.width : ℝ)^BudgetBound.tau ∧
      Machine.run Implementation.program n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) st) Root.tapeCount).start Implementation.program) =
        some c ∧
      step Implementation.program c = none ∧
      c.tapes = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Root.tapeCount := by
  obtain ⟨n,c,hn,htrace,hhalt,hout⟩ := root_budget_hoare v shape hs hv f p node scalar st ready x _ rfl
  have hbound := rootBudget_bound depth (volume prime v)
  rw [← shape.width] at hbound
  exact ⟨n,c,(by exact_mod_cast hn : (n : ℝ) ≤ rootBudget depth (volume prime v)).trans hbound,htrace,hhalt,hout⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.RootExecution
