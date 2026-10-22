module

public import IntegerMultBounds.MathlibTM2.Routing.HostEmbedding
public import IntegerMultBounds.MathlibTM2.Routing.SelectivePlacement
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveKeyPass
public import IntegerMultBounds.MathlibTM2.Routing.BadClassifier

/-!
# Shared finite placement for exact selective repair

The old routing bank embeds into one fixed larger bank. Its five counters are
also the first five key counters and all five classifier counters. The sixth
key counter is the row. All other key/classifier scratch has separate roles.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

deriving instance Fintype for BadReg

/-- Additional input words required by keying and repair setup. -/
inductive RepairExtra where
  | row | keyDescriptor | keyMask | badMask | badPhase | payload | keyLength
  deriving DecidableEq

instance : Fintype RepairExtra :=
  Fintype.ofList [.row, .keyDescriptor, .keyMask, .badMask, .badPhase, .payload, .keyLength]
    (by intro key; cases key <;> simp)

inductive RepairReg where
  | field (f : Fin 6)
  | routing (r : SelectiveReg)
  | key (r : PatternReg 6)
  | bad (r : BadReg)
  | acc | payload | keyLength
  | config (key : RepairExtra)
  deriving DecidableEq, Fintype

abbrev repairT : ℕ := Fintype.card RepairReg

def repairReg : RepairReg → Fin repairT := Fintype.equivFin _

@[simp] theorem repairReg_inj {r s : RepairReg} : repairReg r = repairReg s ↔ r = s :=
  (Fintype.equivFin RepairReg).injective.eq_iff

def repairRoutingRole : SelectiveReg → RepairReg
  | .field f => .field f.castSucc
  | r => .routing r

theorem repairRoutingRole_injective : Function.Injective repairRoutingRole := by
  intro r s he
  cases r <;> cases s <;> simp_all [repairRoutingRole]

def repairRoutingEmbed (j : Fin selectiveT) : Fin repairT :=
  repairReg (repairRoutingRole ((Fintype.equivFin SelectiveReg).symm j))

theorem repairRoutingEmbed_injective : Function.Injective repairRoutingEmbed :=
  (Fintype.equivFin RepairReg).injective.comp
    (repairRoutingRole_injective.comp (Fintype.equivFin SelectiveReg).symm.injective)

@[simp] theorem repairRoutingEmbed_reg (r : SelectiveReg) :
    repairRoutingEmbed (selectiveReg r) = repairReg (repairRoutingRole r) := by
  simp [repairRoutingEmbed, selectiveReg]

def repairHost : SelectiveHost repairT := placedSelectiveHost.map repairRoutingEmbed

def repairRoutingConfig (key : SetupKey) : Fin repairT :=
  repairRoutingEmbed (placedSelectiveConfig key)

theorem repairHost_valid : repairHost.Valid :=
  placedSelectiveHost_valid.map repairRoutingEmbed repairRoutingEmbed_injective

theorem repairHost_setup : SetupLayout repairHost repairRoutingConfig :=
  placedSelectiveHost_setup.map repairRoutingEmbed repairRoutingEmbed_injective

@[simp] theorem repairHost_cf (f : Fin 5) : repairHost.cf f = repairReg (.field f.castSucc) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

def repairKey : PatternReg 6 → Fin repairT
  | .fld f => repairReg (.field f)
  | r => repairReg (.key r)

def repairBad : BadReg → Fin repairT
  | .fld f => repairReg (.field f.castSucc)
  | r => repairReg (.bad r)

theorem repairKey_injective : Function.Injective repairKey := by
  intro r s he
  cases r <;> cases s <;> simp_all [repairKey]

theorem repairBad_injective : Function.Injective repairBad := by
  intro r s he
  cases r <;> cases s <;> simp_all [repairBad]

@[simp] theorem repairKey_cf (f : Fin 5) : repairKey (.fld f.castSucc) = repairHost.cf f := by
  simp [repairKey]

@[simp] theorem repairBad_cf (f : Fin 5) : repairBad (.fld f) = repairHost.cf f := by
  simp [repairBad]

@[simp] theorem repairHost_src : repairHost.src = repairReg (.routing .src) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

@[simp] theorem repairHost_tmp : repairHost.tmp = repairReg (.routing .tmp) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

theorem repairKey_src (r : PatternReg 6) : repairKey r ≠ repairHost.src := by
  cases r <;> simp [repairKey]

theorem repairKey_acc (r : PatternReg 6) : repairKey r ≠ repairReg .acc := by
  cases r <;> simp [repairKey]

theorem repairKey_driver : KeyDriverRegs (fun f => repairKey (.fld f))
    repairHost.src (repairReg .acc) (repairReg .payload) repairHost.tmp where
  regs := by simp
  fields := by intro f g he; simpa [repairKey] using he
  separate f := by simp [repairKey]

theorem repairHost_swapT : swapT 6 ≤ repairT := by
  have h := Fintype.card_le_of_injective (fun j => repairHost.swaps 0 j)
    (repairHost_valid.swap_inj 0)
  simpa using h

@[simp] theorem repairHost_dst (d : Fin 2) : repairHost.dst d = repairReg (.routing (.dst d)) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

@[simp] theorem repairHost_aux (d : Fin 2) : repairHost.aux d = repairReg (.routing (.aux d)) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

@[simp] theorem repairHost_ctr : repairHost.ctr = repairReg (.routing .ctr) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

@[simp] theorem repairHost_cnt : repairHost.cnt = repairReg (.routing .cnt) := by
  simp [repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

theorem repairBad_src (r : BadReg) : repairBad r ≠ repairHost.src := by
  cases r <;> simp [repairBad]

theorem repair_scan_index_separate :
    ∀ x ∈ [repairHost.src, repairHost.dst 0, repairHost.dst 1, repairHost.aux 0, repairHost.aux 1,
      repairHost.ctr, repairHost.cnt, repairHost.tmp], ¬ (∃ r, repairBad r = x) := by
  intro x hx ⟨r, he⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases r <;> simp [repairBad] at he

theorem repair_scan_regs :
    [repairHost.src, repairHost.dst 0, repairHost.dst 1, repairHost.aux 0, repairHost.aux 1,
      repairHost.ctr, repairReg .payload, repairReg .keyLength, repairHost.cnt, repairHost.tmp].Nodup := by
  simp

theorem repair_sort_separate (r : Fin 4) : repairBad (.spare r) ∉
    [repairHost.src, repairHost.dst 0, repairHost.dst 1, repairHost.aux 0, repairHost.aux 1,
      repairHost.ctr, repairReg .payload, repairReg .keyLength, repairHost.cnt, repairHost.tmp] := by
  simp [repairBad]

theorem repair_sort_injective : Function.Injective (fun r : Fin 4 => repairBad (.spare r)) := by
  intro r s he
  simpa [repairBad] using he

theorem repair_sort_fields (r : Fin 4) (f : Fin 5) : repairBad (.spare r) ≠ repairBad (.fld f) := by
  simp [repairBad]

theorem repair_fields_payload (f : Fin 5) : repairBad (.fld f) ≠ repairReg .payload := by
  simp [repairBad]

theorem repair_fields_keyLength (f : Fin 5) : repairBad (.fld f) ≠ repairReg .keyLength := by
  simp [repairBad]

end
end IntegerMultBounds.MathlibTM2.Routing
