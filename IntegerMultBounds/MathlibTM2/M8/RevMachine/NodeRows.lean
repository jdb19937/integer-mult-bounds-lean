module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeBank

/-!
# The row split and merge of a reversed node

The node splits the rows of its input over the contract roles (`split_runs`), as stage 1 does
(`RecursiveRowsNode.entry`): the node view stack saves the headers, every contract role gets its
rows and the headers become the role view's. The temporaries are filled with the zero bit
(`tempInit`) and cleared again before the merge (`tempClear`). The merge (`merge_runs`) takes the
role streams back to `io` through the network's route.

Between the split and the merge the role data is free, up to a blank `io` tape (`NodeData`).
Every such data with blank temporaries is the split of some input (`roleData_surjective`), so
the merge accepts it.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeRows

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open GraphContract (Runs)
open CommonBank (bank K)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRoleSerialization (roles)
open RecursiveRowsSerialization (sourceData roleData putData roleLocal)
open NodeBank (tapes io wires wireSlot tempSlot roleBlock role_runs)

/-! ### Every family of role arrays is a split -/

theorem roleArray_surjective {c : ℕ} {v : Descriptor} (hd : c ∣ v.rows)
    (g : Fin c → Fin (volume prime (role v c)) → Fin 4) :
    ∃ x : Fin (volume prime v) → Fin 4, ∀ j, RecursiveRowsSerialization.roleArray hd x j = g j := by
  refine ⟨fun idx =>
    let ik := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd) idx)
    let jk := finProdFinEquiv.symm ik.2
    g jk.1 (Fin.cast (RecursiveInterchangeRows.role_volume prime c v).symm (finProdFinEquiv (ik.1, jk.2))),
    fun j => ?_⟩
  funext z
  have he := finProdFinEquiv.apply_symm_apply
    (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)
  simp only [finProdFinEquiv_symm_apply] at he
  simp [RecursiveRowsSerialization.roleArray, RecursiveInterchangeRows.roleArray,
    RecursiveInterchangeRows.view, RecursiveInterchangeRows.pack, he]

variable (N : RevNetwork)

/-- The role data between the split and the merge: `io` is blank. -/
def NodeData {v : Descriptor} (data : RecursiveRowsSerialization.Data (tapes N) v) : Prop :=
  data (io N) = fun _ => blank

/-- A temporary is blank. -/
def TempsBlank {v : Descriptor} (data : RecursiveRowsSerialization.Data (tapes N) v) : Prop :=
  ∀ k, data (tempSlot N k) = fun _ => blank

theorem roleData_surjective {v : Descriptor} (hd : N.roleCount ∣ v.rows)
    (data : RecursiveRowsSerialization.Data (tapes N) (role v N.roleCount))
    (hio : NodeData N data) (ht : TempsBlank N data) :
    ∃ x : Fin (volume prime v) → Fin 4, roleData (wires N) (NodeBank.mergeRoute N) hd x = data := by
  obtain ⟨x, hx⟩ := roleArray_surjective hd
    (fun j => data (wires N (Fin.natAdd 1 (NodeBank.mergeRoute N j))))
  refine ⟨x, funext fun i => ?_⟩
  unfold roleData putData
  split_ifs with h
  · have hc := h.choose_spec
    generalize h.choose = j at hc
    subst hc
    induction j using Fin.addCases with
    | left j =>
      have : j = 0 := Subsingleton.elim _ _
      subst this
      simp only [roleLocal, Fin.addCases_left, NodeBank.wires_zero]
      exact hio.symm
    | right j =>
      simp only [roleLocal, Fin.addCases_right, hx, Equiv.apply_symm_apply]
  · push Not at h
    by_cases hi : i = io N
    · exact absurd (by rw [hi]; exact NodeBank.wires_zero N) (h _)
    obtain ⟨w, rfl⟩ := NodeBank.eq_wireSlot N i hi
    cases w with
    | inl r =>
      exact absurd (by simp [wires, Equiv.apply_symm_apply]) (h (Fin.natAdd 1 (N.roleEquiv.symm r)))
    | inr k =>
      have := ht (N.tempEquiv.symm k)
      simp only [tempSlot, Equiv.apply_symm_apply] at this
      exact this.symm

/-! ### The blocks -/

/-- The row split over the contract roles. -/
def split : Graph.Block (CommonBank.count (tapes N)) prime :=
  roleBlock (RecursiveRowsNode.entry (u := Shared50RecursiveBank.AuxCount K - 1) (wires N)
    (NodeBank.wires_injective N))

/-- The row merge through the route. -/
def merge : Graph.Block (CommonBank.count (tapes N)) prime :=
  roleBlock (RecursiveRowsNode.exit (u := Shared50RecursiveBank.AuxCount K - 1) (NodeBank.mergeRoute N)
    (wires N) (NodeBank.wires_injective N))

theorem temp_ne_io (k : Fin N.tempCount) : io N ≠ tempSlot N k := (NodeBank.wireSlot_ne_io N _).symm

/-- Fill every temporary with the symbol `s`, reading `io`. -/
def tempOps (s : Fin 4) : List (Machine.RoleOps.Op (tapes N)) :=
  (List.finRange N.tempCount).map fun k => .fill ⟨io N, tempSlot N k, temp_ne_io N k⟩ s

theorem run_fills {v : Descriptor} (ks : List (Fin N.tempCount)) (s : Fin 4)
    (data : RecursiveMixedSchedule.Data (tapes N) v) (i : Fin (tapes N)) :
    Machine.RoleOps.run (ks.map fun k => Machine.RoleOps.Op.fill ⟨io N, tempSlot N k, temp_ne_io N k⟩ s) data i =
      if ∃ k ∈ ks, tempSlot N k = i then fun _ => s else data i := by
  induction ks generalizing data with
  | nil => simp [Machine.RoleOps.run]
  | cons k ks ih =>
    change Machine.RoleOps.run (ks.map _) (Machine.RoleOps.transform _ data) i = _
    rw [ih]
    simp only [Machine.RoleOps.transform, List.mem_cons, exists_eq_or_imp]
    by_cases hk : tempSlot N k = i
    · subst hk; simp
    · simp only [hk, false_or]
      split_ifs <;> simp [Function.update_of_ne (Ne.symm hk)]

theorem run_tempOps {v : Descriptor} (s : Fin 4) (data : RecursiveMixedSchedule.Data (tapes N) v) :
    (Machine.RoleOps.run (tempOps N s) data (io N) = data (io N)) ∧
      ∀ k, Machine.RoleOps.run (tempOps N s) data (tempSlot N k) = fun _ => s := by
  refine ⟨?_, fun k => ?_⟩
  · rw [tempOps, run_fills]
    rw [ite_eq_right_iff.mpr]
    rintro ⟨k, -, hk⟩
    exact absurd hk.symm (temp_ne_io N k)
  · rw [tempOps, run_fills, ite_eq_left_iff.mpr (fun h => absurd ⟨k, List.mem_finRange k, rfl⟩ h)]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeRows
