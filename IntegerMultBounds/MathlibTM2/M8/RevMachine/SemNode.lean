module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemCall
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemLeaf

/-!
# The node's data from the split to the merge

The split puts the rows of the middle view on the contract roles (`roleBits`, `split_represents`):
on every fiber of the role view, the node's data represents the streams of the rows, with zero
temporaries (`init`). After the pieces the contract roles hold the routed reversed interchange
(`SemPieces.schedule_identity`), and the merge, routing the roles back, gives the reversed
interchange of the middle view (`merge_revT`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume index role)
open RecursiveInterchangeRows (pack rowLength groups)
open RecursiveRowsSerialization (roleData roleArray)
open RecursiveRoleSerialization (roles)
open NodeBank (tapes io wireSlot wires tempSlot)
open NodeSplit (midView roleView NodeInv zeroBit)
open Matrix

/-! ### Rows -/

section Rows

variable {c : ℕ} {v : Descriptor}

private theorem pack_lt' {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- The cell of role `j` at a role index: row `c g + j` of the parent. -/
theorem split_cell (hd : c ∣ v.rows) (j : Fin c) (z : Fin (volume prime (role v c)))
    {a g before h mid d after : ℕ} (hz : z.val = index prime (role v c) a g before h mid d after)
    (hb : before < v.beforeH) (hh : h < prime ^ v.width) (hm : mid < v.between) (hd' : d < prime ^ v.width)
    (haf : after < v.afterD) :
    (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
      (pack (finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)).1
        (pack j (finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)).2))).val =
      index prime v a (c * g + j) before h mid d after := by
  simp only [Fin.val_cast, RecursiveInterchangeRows.pack_val, finProdFinEquiv_symm_apply, Fin.coe_divNat,
    Fin.coe_modNat]
  obtain ⟨S, hSd⟩ : ∃ S, S = (((before * prime ^ v.width + h) * v.between + mid) * prime ^ v.width + d) * v.afterD + after :=
    ⟨_, rfl⟩
  have hS : S < rowLength prime v := by
    rw [hSd]; exact pack_lt' (pack_lt' (pack_lt' (pack_lt' hb hh) hm) hd') haf
  have hRL : 0 < rowLength prime v := by omega
  have hz' : z.val = (a * (v.rows / c) + g) * rowLength prime v + S := by
    rw [hz, hSd]; simp only [index, role, rowLength]; ring
  have q1 : ((a * (v.rows / c) + g) * rowLength prime v + S) / rowLength prime v = a * (v.rows / c) + g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hRL, Nat.div_eq_of_lt hS, zero_add]
  have q2 : ((a * (v.rows / c) + g) * rowLength prime v + S) % rowLength prime v = S := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hS]
  rw [hz', q1, q2]
  have hrows : v.rows / c * c = v.rows := Nat.div_mul_cancel hd
  have e : index prime v a (c * g + j) before h mid d after = (a * v.rows + (c * g + j)) * rowLength prime v + S := by
    rw [hSd]; simp only [index, rowLength]; ring
  rw [e, show a * v.rows = a * (v.rows / c) * c by rw [Nat.mul_assoc, hrows]]
  ring

/-- The bits of role `j`'s rows. -/
def roleBits (hd : c ∣ v.rows) (Y : Fin (volume prime v) → ZMod 2) (j : Fin c) (z : Fin (volume prime (role v c))) :
    ZMod 2 :=
  Y (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
    (pack (finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)).1
      (pack j (finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime c v) z)).2)))

theorem encode_roleBits (hd : c ∣ v.rows) (Y : Fin (volume prime v) → ZMod 2) (j : Fin c)
    (z : Fin (volume prime (role v c))) :
    SparseRoleCircuit.encode (a := 0) (roleBits hd Y j z) =
      roleArray hd (Shared50RecursiveNodeSemantics.encoded Y) j z := rfl

theorem roleArray_cell (hd : c ∣ v.rows) (X : Fin (volume prime v) → Fin 4) (j : Fin c)
    (z : Fin (volume prime (role v c))) {a g before h mid d after : ℕ}
    (hz : z.val = index prime (role v c) a g before h mid d after) (hb : before < v.beforeH)
    (hh : h < prime ^ v.width) (hm : mid < v.between) (hd' : d < prime ^ v.width) (haf : after < v.afterD)
    (hlt : index prime v a (c * g + j) before h mid d after < volume prime v) :
    roleArray hd X j z = X ⟨_, hlt⟩ :=
  congrArg X (Fin.ext (split_cell hd j z hz hb hh hm hd' haf))

theorem roleBits_cell (hd : c ∣ v.rows) (Y : Fin (volume prime v) → ZMod 2) (j : Fin c)
    (z : Fin (volume prime (role v c))) {a g before h mid d after : ℕ}
    (hz : z.val = index prime (role v c) a g before h mid d after) (hb : before < v.beforeH)
    (hh : h < prime ^ v.width) (hm : mid < v.between) (hd' : d < prime ^ v.width) (haf : after < v.afterD)
    (hlt : index prime v a (c * g + j) before h mid d after < volume prime v) :
    roleBits hd Y j z = Y ⟨_, hlt⟩ :=
  congrArg Y (Fin.ext (split_cell hd j z hz hb hh hm hd' haf))

theorem encode_injective : Function.Injective (SparseRoleCircuit.encode (a := 0)) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | exact absurd h (by decide)

end Rows

/-! ### The schedule at the machine prime -/

section Run97

variable {b f : ℕ}

local instance : NeZero (prime ^ b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The pieces of the stage-2 PR97 schedule on streams at the machine prime. -/
def run97 (ps : List (Graph.Piece (Schedule.Seg (rev97m.World ⊕ rev97m.Temp) rev97m.width)
    (Schedule.Call (rev97m.World ⊕ rev97m.Temp)))) (x : Streams' rev97m f b) : Streams' rev97m f b :=
  schedRun rev97m b f ps x

variable (ps : List (Graph.Piece (Schedule.Seg (rev97m.World ⊕ rev97m.Temp) rev97m.width)
    (Schedule.Call (rev97m.World ⊕ rev97m.Temp)))) (x : Streams' rev97m f b)

theorem run97_nil : run97 [] x = x := rfl

theorem run97_edge (w : rev97m.World ⊕ rev97m.Temp) (ops : FieldProgram rev97m.width) :
    run97 (ps ++ [.seg (.edge w ops)]) x = Function.update (run97 ps x) w
      (Rev.twEdgeAction (atomScalar prime b f) (TwistedExchange.atomRev f) ops (run97 ps x w)) := by
  exact schedRun_append rev97m b f ps _ x

theorem run97_gate (g : Circuit.Gate (rev97m.World ⊕ rev97m.Temp) (ZMod 2)) :
    run97 (ps ++ [.seg (.gate g)]) x = FramedCircuit.moduleGate g (run97 ps x) := by
  exact schedRun_append rev97m b f ps _ x

theorem run97_reset (w : rev97m.World ⊕ rev97m.Temp) :
    run97 (ps ++ [.seg (.reset w)]) x = Function.update (run97 ps x) w 0 := by
  exact schedRun_append rev97m b f ps _ x

theorem run97_call (c : Schedule.Call (rev97m.World ⊕ rev97m.Temp)) :
    run97 (ps ++ [.call c]) x = Function.update (run97 ps x) c.1
      (Rev.twEdgeAction (atomScalar prime b f) (TwistedExchange.atomRev f)
        (Exchange.swapOps (ReversedExchange.revPivots rev97m.width c.2)) (run97 ps x c.1)) := by
  exact schedRun_append rev97m b f ps _ x

/-- **The node theorem** at the machine prime. -/
theorem run97_identity (stored : Streams' rev97m f b) (hz : ∀ t, stored (.inr t) = 0) (i : rev97m.World)
    (a : Rev.Addr rev97m.width (SA f b)) :
    run97 (RevHalf.pcs rev97m) stored (.inl i) a = stored (.inl (rev97m.route i))
      (TwistedExchange.twist (TwistedExchange.atomRev f) (Rev.revS (d := rev97m.width) (atomScalar prime b f) *ᵥ a.2),
        TwistedExchange.twist (TwistedExchange.atomRev f) (Rev.revS (d := rev97m.width) (atomScalar prime b f) *ᵥ a.1)) :=
  schedule_identity rev97m b f edgeForm97 stored hz i a

end Run97

/-! ### The split's streams -/

variable {b n : ℕ} {v : Descriptor}

local instance : NeZero (prime ^ b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- The middle view's bits of a frame's bits. -/
def midBits (hw : v.width = n * b) (Y : Fin (volume prime v) → ZMod 2) :
    Fin (volume prime (midView rev97m b n v)) → ZMod 2 :=
  fun i => Y (Fin.cast (NodeSplit.mid_volume rev97m hw) i)

/-- **The streams of the split** on the fiber of `x`: the rows on the contract roles, zero
temporaries. -/
def init (hd : rev97m.roleCount ∣ v.rows) (Ym : Fin (volume prime (midView rev97m b n v)) → ZMod 2)
    (x : RecursiveScalarCoordinates.Address (rev97m.width * (n / rev97m.width)) b (roleView rev97m b n v)) :
    Streams' rev97m (n / rev97m.width) b
  | .inl i, s => roleBits (NodeSplit.mid_dvd rev97m hd) Ym (rev97m.roleEquiv.symm i) (pos rfl x s)
  | .inr _, _ => 0

/-- **The split represents the rows.** -/
theorem split_represents (hw : v.width = n * b) (hd : rev97m.roleCount ∣ v.rows) (Y : Fin (volume prime v) → ZMod 2)
    (x : RecursiveScalarCoordinates.Address (rev97m.width * (n / rev97m.width)) b (roleView rev97m b n v)) :
    Represents rev97m rfl x (NodeSplit.splitData rev97m hw hd (Shared50RecursiveNodeSemantics.encoded Y))
      (init hd (midBits hw Y) x) := by
  intro w s
  cases w with
  | inl i =>
    have hk : ¬ ∃ k ∈ List.finRange rev97m.tempCount, tempSlot rev97m k = wireSlot rev97m (.inl i) := by
      rintro ⟨k, -, hk⟩
      have := NodeBank.wireSlot_injective rev97m hk
      simp at this
    have he : wireSlot rev97m (.inl i) = wires rev97m (Fin.natAdd 1 (rev97m.roleEquiv.symm i)) := by
      simp [wires]
    simp only [NodeSplit.splitData]
    erw [NodeRows.tempOps, NodeRows.run_fills, ite_eq_right hk, he,
      RecursiveRowsSerialization.roleData_entry _ (NodeBank.wires_injective rev97m)]
    rfl
  | inr t =>
    have ht := (NodeRows.run_tempOps rev97m zeroBit
      (roleData (wires rev97m) (Equiv.refl _) (NodeSplit.mid_dvd rev97m hd)
        (fun i => Shared50RecursiveNodeSemantics.encoded Y (Fin.cast (NodeSplit.mid_volume rev97m hw) i)))).2
      (rev97m.tempEquiv.symm t)
    simp only [tempSlot, Equiv.apply_symm_apply] at ht
    simp only [NodeSplit.splitData]
    erw [ht]
    rfl

/-! ### The merge -/

/-- **The merge's reversed interchange.** If the node's data represents the schedule's run of the
split's streams on every fiber, the merged array of the middle view is its reversed interchange. -/
theorem merge_revT (hd : rev97m.roleCount ∣ v.rows) (Ym : Fin (volume prime (midView rev97m b n v)) → ZMod 2)
    (data : RecursiveMixedSchedule.Data (tapes rev97m) (roleView rev97m b n v))
    (hrep : ∀ x, Represents rev97m rfl x data
      (run97 (RevHalf.pcs rev97m) (init hd Ym x)))
    (Y' : Fin (volume prime (midView rev97m b n v)) → ZMod 2)
    (hY : roleData (wires rev97m) (NodeBank.mergeRoute rev97m) (NodeSplit.mid_dvd rev97m hd)
      (Shared50RecursiveNodeSemantics.encoded Y') = Machine.RoleOps.run (NodeRows.tempOps rev97m blank) data) :
    RevT prime b (rev97m.width * (n / rev97m.width)) (midView rev97m b n v) (ext Ym) (ext Y') := by
  intro a ha row hrow before hb H hH mid hm D hD after haf
  have hW : 0 < rev97m.roleCount := by
    rcases Nat.eq_zero_or_pos rev97m.roleCount with h0 | h0
    · rw [h0, zero_dvd_iff] at hd
      have : row < v.rows := hrow
      omega
    · exact h0
  set g := row / rev97m.roleCount
  set j : Fin rev97m.roleCount := ⟨row % rev97m.roleCount, Nat.mod_lt _ hW⟩
  have hrow' : row = rev97m.roleCount * g + j.val := (Nat.div_add_mod row rev97m.roleCount).symm
  have hg : g < (roleView rev97m b n v).rows := Nat.div_lt_div_of_lt_of_dvd hd hrow
  obtain ⟨x, s, hp1, hp2⟩ := full_pos (v := roleView rev97m b n v) (m := rev97m.width) (f := n / rev97m.width) (b := b) rfl
    ha hg hb hH hm hD haf
  have hQ : 0 < prime ^ b := pow_pos Networks.Shared50ModularControl.prime_prime.pos b
  have hrD : revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) D < prime ^ (midView rev97m b n v).width := by
    rw [show (midView rev97m b n v).width = (rev97m.width * (n / rev97m.width)) * b from rfl, prime_pow_mul]; exact revAtoms_lt hQ _ _
  have hrH : revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) H < prime ^ (midView rev97m b n v).width := by
    rw [show (midView rev97m b n v).width = (rev97m.width * (n / rev97m.width)) * b from rfl, prime_pow_mul]; exact revAtoms_lt hQ _ _
  have hlt1 : index prime (midView rev97m b n v) a (rev97m.roleCount * g + j.val) before H mid D after < volume prime (midView rev97m b n v) :=
    index_lt ha (by rw [← hrow']; exact hrow) hb hH hm hD haf
  have hlt2 : index prime (midView rev97m b n v) a (rev97m.roleCount * g + j.val) before (revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) D) mid
      (revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) H) after < volume prime (midView rev97m b n v) :=
    index_lt ha (by rw [← hrow']; exact hrow) hb hrD hm hrH haf
  have L : ext Y' (index prime (midView rev97m b n v) a row before H mid D after) = Y' ⟨_, hlt1⟩ := by
    rw [hrow']; simp only [ext, hlt1, ↓reduceDIte]
  have R : ext Ym (index prime (midView rev97m b n v) a row before (revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) D) mid
      (revAtoms (prime ^ b) (rev97m.width * (n / rev97m.width)) H) after) = Ym ⟨_, hlt2⟩ := by
    rw [hrow']; simp only [ext, hlt2, ↓reduceDIte]
  rw [L, R]
  apply encode_injective
  have c1 := roleArray_cell (NodeSplit.mid_dvd rev97m hd) (Shared50RecursiveNodeSemantics.encoded Y') j (pos rfl x s) hp1 hb hH hm hD
    haf hlt1
  have c2 := RecursiveRowsSerialization.roleData_entry (wires rev97m) (NodeBank.wires_injective rev97m)
    (NodeBank.mergeRoute rev97m) (NodeSplit.mid_dvd rev97m hd) (Shared50RecursiveNodeSemantics.encoded Y') (NodeBank.mergeRoute rev97m j)
    (pos rfl x s)
  rw [Equiv.symm_apply_apply, hY, NodeSplit.merge_world] at c2
  have hwire : wires rev97m (Fin.natAdd 1 (NodeBank.mergeRoute rev97m j)) =
      wireSlot rev97m (.inl (rev97m.roleEquiv (NodeBank.mergeRoute rev97m j))) := by simp [wires]
  rw [hwire, hrep x (.inl _) s, run97_identity _ (fun t => funext fun _ => rfl)] at c2
  have hroute : rev97m.route (rev97m.roleEquiv (NodeBank.mergeRoute rev97m j)) = rev97m.roleEquiv j := by
    simp only [NodeBank.mergeRoute, Equiv.trans_apply, Equiv.apply_symm_apply]
    exact rev97m.route_involutive _
  rw [hroute] at c2
  simp only [init, Equiv.symm_apply_apply] at c2
  have c3 := roleBits_cell (NodeSplit.mid_dvd rev97m hd) Ym j _ hp2 hb hrD hm hrH haf hlt2
  calc SparseRoleCircuit.encode (a := 0) (Y' ⟨_, hlt1⟩) = roleArray (NodeSplit.mid_dvd rev97m hd) (Shared50RecursiveNodeSemantics.encoded Y') j (pos rfl x s) := c1.symm
    _ = SparseRoleCircuit.encode (a := 0) (roleBits (NodeSplit.mid_dvd rev97m hd) Ym j (pos rfl x _)) := c2.symm
    _ = SparseRoleCircuit.encode (a := 0) (Ym ⟨_, hlt2⟩) := by rw [c3]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
