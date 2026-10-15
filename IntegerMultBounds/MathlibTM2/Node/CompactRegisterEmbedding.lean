module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRegisters
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! A fixed embedding preserves every ordinary layer register while placing
the two private basis workspaces in disjoint parts of one fixed bank. This allows the checked
original-input constructors to run directly beside the compact layer. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
noncomputable section

/-- The construction and compact execution keep distinct private banks while
sharing every ordinary layer register. This is one fixed finite host bank. -/
abbrev CompactHostBReg := CompactBReg ⊕ SXReg

variable {BReg BReg' : Type}

def compactMapRegName (f : BReg → BReg') : LReg BReg → LReg BReg'
  | .io => .io
  | .wire x => .wire x
  | .wtmp x => .wtmp x
  | .park => .park
  | .ctr => .ctr
  | .tmp => .tmp
  | .cS => .cS
  | .cR => .cR
  | .tS => .tS
  | .tR => .tR
  | .ph x => .ph x
  | .lf x => .lf x
  | .rowctr => .rowctr
  | .rowtmp => .rowtmp
  | .rctmp => .rctmp
  | .racc => .racc
  | .lenctr => .lenctr
  | .lev => .lev
  | .u => .u
  | .K => .K
  | .ρ => .ρ
  | .a₀ => .a₀
  | .L => .L
  | .rows => .rows
  | .n => .n
  | .w => .w
  | .rw => .rw
  | .Tc => .Tc
  | .sc x => .sc x
  | .bc x => .bc (f x)
  | .st => .st
  | .cs => .cs

lemma compactMapRegName_injective {f : BReg → BReg'} (hf : Function.Injective f) :
    Function.Injective (compactMapRegName f) := by
  intro x y h
  cases x <;> cases y <;> simp_all [compactMapRegName,hf.eq_iff]

variable [Fintype BReg] [Fintype BReg']

def compactMapReg (f : BReg → BReg') (i : Fin (nT BReg)) : Fin (nT BReg') :=
  reg (compactMapRegName f ((regEquiv BReg).symm i))

lemma compactMapReg_injective {f : BReg → BReg'} (hf : Function.Injective f) :
    Function.Injective (compactMapReg f) :=
  reg_injective.comp ((compactMapRegName_injective hf).comp (regEquiv BReg).symm.injective)

@[simp] lemma compactMapReg_reg (f : BReg → BReg') (x : LReg BReg) :
    compactMapReg f (reg x)=reg (compactMapRegName f x) := by
  simp [compactMapReg,reg]

/-- Placement of the call-free original-input construction. -/
def compactLegacyReg : Fin (nT SXReg) → Fin (nT CompactHostBReg) :=
  compactMapReg Sum.inr

/-- Placement of the complete recursive compact layer. -/
def compactLayerReg : Fin (nT CompactBReg) → Fin (nT CompactHostBReg) :=
  compactMapReg Sum.inl

lemma compactLegacyReg_injective : Function.Injective compactLegacyReg :=
  compactMapReg_injective Sum.inr_injective

lemma compactLayerReg_injective : Function.Injective compactLayerReg :=
  compactMapReg_injective Sum.inl_injective

@[simp] lemma compactLegacyReg_wire (x : Layer.NWire) :
    compactLegacyReg (reg (.wire x))=reg (.wire x) := by
  simp [compactLegacyReg,compactMapRegName]

@[simp] lemma compactLayerReg_wire (x : Layer.NWire) :
    compactLayerReg (reg (.wire x))=reg (.wire x) := by
  simp [compactLayerReg,compactMapRegName]

@[simp] lemma compactLegacyReg_io : compactLegacyReg (reg .io)=reg .io := by
  simp [compactLegacyReg,compactMapRegName]

@[simp] lemma compactLayerReg_io : compactLayerReg (reg .io)=reg .io := by
  simp [compactLayerReg,compactMapRegName]

/-- The constructor's placement cannot touch persistent compact basis inputs. -/
lemma compactLegacyReg_ne_compact_bc (i : Fin (nT SXReg)) (x : CompactBReg) :
    compactLegacyReg i ≠ reg (.bc (Sum.inl x : CompactHostBReg)) := by
  intro h
  have hh := reg_injective h
  change compactMapRegName Sum.inr ((regEquiv SXReg).symm i)=.bc (Sum.inl x) at hh
  generalize (regEquiv SXReg).symm i=y at hh
  cases y <;> simp [compactMapRegName] at hh

/-- Compact recursive execution cannot touch the constructor's private bank. -/
lemma compactLayerReg_ne_legacy_bc (i : Fin (nT CompactBReg)) (x : SXReg) :
    compactLayerReg i ≠ reg (.bc (Sum.inr x : CompactHostBReg)) := by
  intro h
  have hh := reg_injective h
  change compactMapRegName Sum.inl ((regEquiv CompactBReg).symm i)=.bc (Sum.inr x) at hh
  generalize (regEquiv CompactBReg).symm i=y at hh
  cases y <;> simp [compactMapRegName] at hh

end
end IntegerMultBounds.MathlibTM2.LayerMachine
