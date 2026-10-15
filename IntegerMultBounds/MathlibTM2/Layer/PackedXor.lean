module

public import IntegerMultBounds.Compact.RepairPipeline
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

/-!
# Packed XOR of selected address bits

Records are addressed by
`[N₀] × [2^L]_{χ₁} × [N₁] × [2^L]_{χ₂} × [N₂] × [2^L]_{χ₃} × [N₃]` with `L = f K`. The three
`L`-bit chunks carry the names `x = 0`, `y = 1`, `z = 2`; a physical order `σ : Perm (Fin 3)`
places the name `σ k` in chunk slot `k`. The selected positions are `j_i = ρ + i K` (`i < f`,
`ρ < K`), numbered from the least significant bit.

**Target** (`xorSel`): `y_{j_i} ← y_{j_i} ⊕ x_{j_i}` for every `i < f`; all other bits of `y`,
all of `x` and `z`, and the spectators are unchanged (`xorSel_spec`). `liftA` lifts a map of
triples to record addresses, and `enc σ` sends a logical address to its lexicographic rank in
`[M]`, `M = N₀ N₁ N₂ N₃ 2^{3L}` (`rank`, `enc_val`).

**Decomposition** (bundled in `packedXor_main`):
1. *Stream program* `prog σ`. At most two chunk swaps (`toStd σ`) bring the order to
   `(x, z, y)`. The fourteen instructions of `core` are the eight lines of the paper's display
   `eq:eight-packed-additions`, each the rotation of slot 2 by `± offMag b (slot 0) (slot 1)`
   modulo `2^L`, interleaved with six swaps of slots 1 and 2. The first swaps are then undone
   in reverse order. Here
   `offMag b c w = ∑_{i < f-1} 2^{j_i} [c_{j_i} = 1] [w_{j_i} = b]`, so each rotation reads
   exactly `x` and the non-target field, both placed before the target. The program has eight
   rotations and at most ten swaps (`prog_counts`); on logical triples it is `packedS`
   (`prog_spec`, `prog_rank`).
2. *Repair*. `packedS` agrees with `idealT`, the XOR at `j_0, …, j_{f-2}`, off `Bad`
   (`packed_agrees`); both maps preserve `Bad` (`idealT_preserves_bad`,
   `packed_preserves_bad`); hence the vendored extract–sort–fill `pipeline` turns the stream
   after the program into the stream of `idealT` (`repair_exact`). An address is in `Bad` when
   the guard `g = ⌊seg / 2⌋` of some segment `i < f - 1` of `y` or of `z` lies outside
   `[m, 2^{K-1} - 1 - m]`; the guard is `v / 2^{j_i + 1} mod 2^{K-1}` (`guard`).
3. *Fixup*. `topFix`, the elementary two-bit XOR `y_{j_{f-1}} ← y_{j_{f-1}} ⊕ x_{j_{f-1}}`,
   completes the target: `xorSel = topFix * idealT` (`xorSel_eq`, `fixup_after_repair`).
4. *Exceptional count*. `|Bad| · 2^K ≤ 8 m (f-1) M` (`card_bad`), so
   `|Bad| ≤ min 1 (8 m (f-1) 2^{-K}) · M` (`card_bad_le`); the paper's margin `m = 10`
   (guards `10 ≤ g ≤ 2^{K-1} - 11`) gives the constant `80` (`card_bad_le_paper`).

**Choice of gadget.** Each of the eight cyclic additions changes one segment by at most one,
and every intermediate value of a segment `2a + p` stays in `[2a - 1, 2a + 2]` (`safe_lines`).
Target and temporary segments therefore share the radix `2^K`, and each guard excludes `2m` of
its `2^{K-1}` values. The vendored four-update gadget `packedEarly` adds `2 c w`, a whole
temporary digit, to the target digit; its good set `Good B L` (target radix `Q = 2L`,
temporary radix `B`) requires `2B ≤ v/2 < L - 2B`, which is empty for `Q = B = 2^K`. With a
temporary radix `2^b` its bad fraction is `n 2^{-b} + 8 n 2^{b - K}` (`early_bad_fraction_le`),
of order at least `n 2^{-K/2}`. The proof below uses the vendored radix packing (`pack`,
`digits`, `digits_pack`, `pack_bounds`, `rotate_with_spectators`), `toggle`, the abstract
repair lemma `actual_preserves_bad`, and `pipeline_exact`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer.PackedXor

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-! ### Chunk values, rotations, and the target -/

/-- Three `L`-bit chunk values: a logical triple indexed by the names `x = 0`, `y = 1`, `z = 2`,
or the contents of the physical chunk slots `0, 1, 2`. -/
abbrev Tri (L : ℕ) := Fin 3 → Fin (2 ^ L)

/-- Rotation of an `L`-bit chunk value by a signed offset: `v ↦ (v + a) mod 2^L`. -/
def rot (L : ℕ) (v : Fin (2 ^ L)) (a : ℤ) : Fin (2 ^ L) :=
  ⟨(((v : ℤ) + a) % 2 ^ L).toNat, by
    have h0 : (0 : ℤ) < 2 ^ L := by positivity
    have h1 := Int.emod_nonneg ((v : ℤ) + a) h0.ne'
    have h2 := Int.emod_lt_of_pos ((v : ℤ) + a) h0
    have h3 : ((2 ^ L : ℕ) : ℤ) = 2 ^ L := by push_cast; rfl
    omega⟩

/-- The value of a rotation, as an integer. -/
theorem rot_val (L : ℕ) (v : Fin (2 ^ L)) (a : ℤ) :
    (((rot L v a : Fin (2 ^ L)) : ℕ) : ℤ) = ((v : ℤ) + a) % 2 ^ L := by
  have h0 : (0 : ℤ) < 2 ^ L := by positivity
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ h0.ne')

/-- Rotating back by the negated offset restores the value. -/
theorem rot_neg (L : ℕ) (v : Fin (2 ^ L)) (a : ℤ) : rot L (rot L v a) (-a) = v := by
  apply Fin.ext
  have h : (((rot L (rot L v a) (-a) : Fin (2 ^ L)) : ℕ) : ℤ) = ((v : ℕ) : ℤ) := by
    rw [rot_val, rot_val, Int.emod_add_emod, add_neg_cancel_right]
    apply Int.emod_eq_of_lt (by positivity)
    have := v.isLt
    exact_mod_cast this
  exact_mod_cast h

/-- Controlled rotation of entry `t` by the offset `F (v a) (v b)` read from entries `a`, `b`. -/
def crot (L : ℕ) (t a b : Fin 3) (F : ℕ → ℕ → ℤ) (v : Tri L) : Tri L :=
  Function.update v t (rot L (v t) (F (v a) (v b)))

/-- A controlled rotation is a permutation when its target is distinct from both controls;
the inverse rotates by the negated offset. -/
def crotPerm (L : ℕ) (t a b : Fin 3) (F : ℕ → ℕ → ℤ) (ha : t ≠ a) (hb : t ≠ b) :
    Equiv.Perm (Tri L) where
  toFun := crot L t a b F
  invFun := crot L t a b (fun c w => -F c w)
  left_inv v := by
    simp only [crot, Function.update_self, Function.update_of_ne ha.symm,
      Function.update_of_ne hb.symm, Function.update_idem, rot_neg, Function.update_eq_self]
  right_inv v := by
    have h := rot_neg L (v t) (-F (v a) (v b))
    rw [neg_neg] at h
    simp only [crot, Function.update_self, Function.update_of_ne ha.symm,
      Function.update_of_ne hb.symm, Function.update_idem, h, Function.update_eq_self]

/-- Renaming the entries by `σ` transports a controlled rotation to the renamed entries. -/
theorem crot_comp (L : ℕ) (t a b : Fin 3) (F : ℕ → ℕ → ℤ) (v : Tri L) (σ : Equiv.Perm (Fin 3)) :
    crot L t a b F v ∘ σ = crot L (σ.symm t) (σ.symm a) (σ.symm b) F (v ∘ σ) := by
  simp only [crot, Function.update_comp_equiv, Function.comp_apply, Equiv.apply_symm_apply]

/-- The mask `∑_{i < n} 2^{ρ + i K}` of the first `n` selected positions. -/
def selMask (K ρ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => selMask K ρ n ||| 2 ^ (ρ + n * K)

/-- Position `j` is one of the first `n` selected positions `ρ + i K`. -/
def IsSel (K ρ n j : ℕ) : Prop := ∃ i < n, j = ρ + i * K

/-- The bits of `selMask` are exactly the selected positions. -/
theorem testBit_selMask (K ρ n j : ℕ) : (selMask K ρ n).testBit j = true ↔ IsSel K ρ n j := by
  induction n with
  | zero => simp [selMask, IsSel]
  | succ n ih =>
    simp only [selMask, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow,
      decide_eq_true_eq, IsSel]
    constructor
    · rintro (⟨i, hi, rfl⟩ | h)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨n, by omega, h.symm⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr rfl

/-- `y ← y ⊕ (x ∧ M)` on a triple; `x` and `z` are unchanged. -/
def xorMask (L M : ℕ) (v : Tri L) : Tri L :=
  Function.update v 1 ⟨(v 1 : ℕ) ^^^ ((v 0 : ℕ) &&& M),
    Nat.xor_lt_two_pow (v 1).isLt (lt_of_le_of_lt Nat.and_le_left (v 0).isLt)⟩

/-- `xorMask` is an involution. -/
theorem xorMask_xorMask (L M : ℕ) (v : Tri L) : xorMask L M (xorMask L M v) = v := by
  funext k
  have h01 : (1 : Fin 3) ≠ 0 := by decide
  simp only [xorMask, Function.update_self, Function.update_of_ne h01.symm, Function.update_idem]
  by_cases hk : k = 1
  · subst hk
    simp only [Function.update_self]
    apply Fin.ext
    simp
  · simp [Function.update_of_ne hk]

/-- `xorMask` as a permutation of triples. -/
def xorMaskPerm (L M : ℕ) : Equiv.Perm (Tri L) where
  toFun := xorMask L M
  invFun := xorMask L M
  left_inv := xorMask_xorMask L M
  right_inv := xorMask_xorMask L M

section Selected

variable (K ρ n : ℕ)

instance (j : ℕ) : Decidable (IsSel K ρ n j) := by unfold IsSel; infer_instance

end Selected

section Target

variable (L K ρ f : ℕ)

/-- **The target.** `y_{j_i} ← y_{j_i} ⊕ x_{j_i}` at `j_i = ρ + i K` for every `i < f`. -/
def xorSel : Equiv.Perm (Tri L) := xorMaskPerm L (selMask K ρ f)

/-- The ideal map of the packed lines: the XOR at the first `f - 1` selected positions. -/
def idealT : Equiv.Perm (Tri L) := xorMaskPerm L (selMask K ρ (f - 1))

/-- The separate two-bit fixup at the top selected position `j_{f-1}`. -/
def topFix : Equiv.Perm (Tri L) := xorMaskPerm L (2 ^ (ρ + (f - 1) * K))

/-- **Bitwise specification of the target.** `x` and `z` are unchanged and
`y'_j = y_j ⊕ (x_j ∧ [j = ρ + i K for some i < f])`. -/
theorem xorSel_spec (v : Tri L) :
    xorSel L K ρ f v 0 = v 0 ∧ xorSel L K ρ f v 2 = v 2 ∧
    ∀ j, ((xorSel L K ρ f v 1 : Fin (2 ^ L)) : ℕ).testBit j =
      ((v 1 : ℕ).testBit j ^^ ((v 0 : ℕ).testBit j && decide (IsSel K ρ f j))) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  refine ⟨?_, ?_, fun j => ?_⟩
  · change (xorMask L (selMask K ρ f) v) 0 = v 0
    simp only [xorMask, Function.update_of_ne h01]
  · change (xorMask L (selMask K ρ f) v) 2 = v 2
    simp only [xorMask, Function.update_of_ne h21]
  change (((xorMask L (selMask K ρ f) v) 1 : Fin (2 ^ L)) : ℕ).testBit j = _
  simp only [xorMask, Function.update_self, Nat.testBit_xor, Nat.testBit_and]
  congr 2
  rw [Bool.eq_iff_iff, testBit_selMask, decide_eq_true_iff]

end Target

/-! ### The eight packed lines -/

section Offsets

variable (K ρ n : ℕ)

/-- The magnitude of a packed offset: the sum of `2^{j_i}` over the selected positions `j_i`
(`i < n`) where the control `c` has a one and the other field `w` has the bit `b`. -/
def offMag (b : Bool) (c w : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n,
    if c.testBit (ρ + i * K) = true ∧ w.testBit (ρ + i * K) = b then 2 ^ (ρ + i * K) else 0

end Offsets

/-- One line of the eight cyclic additions: it updates `y` (`tgtY = true`) or `z`, subtracts
(`neg = true`) or adds, and tests the selected bits of the other field for the value `b`. -/
structure Line where
  tgtY : Bool
  neg : Bool
  b : Bool
deriving DecidableEq, Repr

/-- The sign of a line. -/
def sgn (neg : Bool) : ℤ := if neg then -1 else 1

/-- The target name of a line: `y = 1` or `z = 2`. -/
def Line.tgt (l : Line) : Fin 3 := if l.tgtY then 1 else 2

/-- The other (tested) name of a line: `z = 2` or `y = 1`. -/
def Line.oth (l : Line) : Fin 3 := if l.tgtY then 2 else 1

/-- The target of a line is never `x`. -/
theorem Line.tgt_ne_zero (l : Line) : l.tgt ≠ 0 := by unfold Line.tgt; split <;> decide

/-- The target of a line differs from the field it tests. -/
theorem Line.tgt_ne_oth (l : Line) : l.tgt ≠ l.oth := by
  unfold Line.tgt Line.oth; split <;> decide

/-- The signed packed offset of a line, from the control value `c = x` and the other value `w`. -/
def Line.offset (K ρ n : ℕ) (l : Line) (c w : ℕ) : ℤ := sgn l.neg * offMag K ρ n l.b c w

/-- A line as a permutation of the triple `(x, y, z)`: its target gains its offset modulo `2^L`;
the offset reads only `x` and the other field. -/
def Line.perm (L K ρ n : ℕ) (l : Line) : Equiv.Perm (Tri L) :=
  crotPerm L l.tgt 0 l.oth (l.offset K ρ n) l.tgt_ne_zero l.tgt_ne_oth

/-- Composition of lines in list order (the head acts first). -/
def linesPerm (L K ρ n : ℕ) : List Line → Equiv.Perm (Tri L)
  | [] => Equiv.refl _
  | l :: ls => (l.perm L K ρ n).trans (linesPerm L K ρ n ls)

/-- The eight lines of `eq:eight-packed-additions`, in chronological order:
`u -= c[w even]`, `w -= c[u even]`, `u += c[w even]`, `w += c[u even]`,
`w += c[u odd]`, `u += c[w odd]`, `w -= c[u odd]`, `u -= c[w odd]`,
with `u` a segment of `y`, `w` the matching segment of `z`, and `c = x_{j_i}`. -/
def lines : List Line :=
  [⟨true, true, false⟩, ⟨false, true, false⟩, ⟨true, false, false⟩, ⟨false, false, false⟩,
   ⟨false, false, true⟩, ⟨true, false, true⟩, ⟨false, true, true⟩, ⟨true, true, true⟩]

section Packed

variable (L K ρ f : ℕ)

/-- The actual packed program `S₀` on logical triples: the eight lines in order. -/
def packedS : Equiv.Perm (Tri L) := linesPerm L K ρ (f - 1) lines

end Packed

/-! ### The stream program -/

/-- Stream instructions on the three chunk slots of a physical address. -/
inductive Instr
  /-- Exchange the equal-width chunks in physical slots `a` and `b`. -/
  | swap (a b : Fin 3)
  /-- Rotate the last chunk (slot 2) by `± offMag b (slot 0) (slot 1)` modulo `2^L`: the offset
  reads only the two chunks that precede the target. -/
  | rot (neg b : Bool)
deriving DecidableEq, Repr

section Program

variable (L K ρ n : ℕ)

/-- The action of one instruction on the chunk-slot values. -/
def Instr.run : Instr → Tri L → Tri L
  | .swap a b, c => c ∘ Equiv.swap a b
  | .rot neg b, c => crot L 2 0 1 (fun c₀ c₁ => sgn neg * offMag K ρ n b c₀ c₁) c

/-- Run a list of instructions, head first. -/
def runProg (P : List Instr) (c : Tri L) : Tri L := P.foldl (fun c i => i.run L K ρ n c) c

/-- Programs compose by concatenation. -/
theorem runProg_append (P P' : List Instr) (c : Tri L) :
    runProg L K ρ n (P ++ P') c = runProg L K ρ n P' (runProg L K ρ n P c) := by
  simp [runProg, List.foldl_append]

/-- Physical slot values of a logical triple when physical slot `k` holds the name `σ k`. -/
def phys (σ : Equiv.Perm (Fin 3)) (v : Tri L) : Tri L := v ∘ σ

/-- The core program, from the physical order `(x, z, y)` back to `(x, z, y)`. Each rotation
targets slot 2, the logical target, and reads `x` in slot 0 and the other field in slot 1. -/
def core : List Instr :=
  [.rot true false, .swap 1 2, .rot true false, .swap 1 2,
   .rot false false, .swap 1 2, .rot false false, .rot false true, .swap 1 2,
   .rot false true, .swap 1 2, .rot true true, .swap 1 2, .rot true true]

/-- In order `(x, z, y)` a rotation is the line on `y` that tests `z`. -/
theorem run_rot_y (neg b : Bool) (v : Tri L) :
    (Instr.rot neg b).run L K ρ n (phys L (Equiv.swap 1 2) v) =
      phys L (Equiv.swap 1 2) ((Line.mk true neg b).perm L K ρ n v) := by
  simp only [Instr.run, phys, Line.perm, crotPerm, Equiv.coe_fn_mk, Line.tgt, Line.oth,
    ite_true, Line.offset, crot_comp, Equiv.symm_swap]
  congr 1

/-- In order `(x, y, z)` a rotation is the line on `z` that tests `y`. -/
theorem run_rot_z (neg b : Bool) (v : Tri L) :
    (Instr.rot neg b).run L K ρ n (phys L 1 v) = phys L 1 ((Line.mk false neg b).perm L K ρ n v) := by
  simp only [Instr.run, phys, Line.perm, crotPerm, Equiv.coe_fn_mk, Line.tgt, Line.oth,
    Bool.false_eq_true, ite_false, Equiv.Perm.coe_one, Function.comp_id]
  rfl

/-- A swap of slots `a`, `b` changes the physical order to `σ * swap a b`. -/
theorem run_swap (a b : Fin 3) (σ : Equiv.Perm (Fin 3)) (v : Tri L) :
    (Instr.swap a b).run L K ρ n (phys L σ v) = phys L (σ * Equiv.swap a b) v := by
  simp only [Instr.run, phys, Equiv.Perm.coe_mul, Function.comp_assoc]

/-- The core program implements the eight lines in the physical order `(x, z, y)`. -/
theorem core_spec (v : Tri L) :
    runProg L K ρ n core (phys L (Equiv.swap 1 2) v) =
      phys L (Equiv.swap 1 2) (linesPerm L K ρ n lines v) := by
  simp only [runProg, core, List.foldl_cons, List.foldl_nil, run_rot_y, run_swap,
    Equiv.swap_mul_self, run_rot_z, one_mul]
  simp only [linesPerm, lines, Equiv.trans_apply, Equiv.refl_apply]

/-- The product of a list of slot transpositions, head first. -/
def swapsPerm (ws : List (Fin 3 × Fin 3)) : Equiv.Perm (Fin 3) :=
  (ws.map (fun w => Equiv.swap w.1 w.2)).prod

/-- A list of slot transpositions as swap instructions. -/
def swapInstrs (ws : List (Fin 3 × Fin 3)) : List Instr := ws.map (fun w => .swap w.1 w.2)

/-- A list of swaps changes the physical order by the product of the transpositions. -/
theorem runProg_swaps (ws : List (Fin 3 × Fin 3)) :
    ∀ (σ : Equiv.Perm (Fin 3)) (v : Tri L),
      runProg L K ρ n (swapInstrs ws) (phys L σ v) = phys L (σ * swapsPerm ws) v := by
  induction ws with
  | nil => intro σ v; simp [swapInstrs, swapsPerm, runProg]
  | cons w ws ih =>
    intro σ v
    have h := ih (σ * Equiv.swap w.1 w.2) v
    simp only [runProg, swapInstrs, List.map_cons, List.foldl_cons] at h ⊢
    rw [run_swap, h]
    simp only [swapsPerm, List.map_cons, List.prod_cons, mul_assoc]

/-- Reversing a list of transpositions inverts their product. -/
theorem swapsPerm_reverse (ws : List (Fin 3 × Fin 3)) :
    swapsPerm ws.reverse = (swapsPerm ws)⁻¹ := by
  unfold swapsPerm
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
  congr 2

/-- Transpositions taking the physical order `σ` to the standard order `(x, z, y)`: first bring
`x` to slot 0, then exchange slots 1 and 2 if `y` is in slot 1. At most two swaps. -/
def toStd (σ : Equiv.Perm (Fin 3)) : List (Fin 3 × Fin 3) :=
  let first : List (Fin 3 × Fin 3) := if σ.symm 0 = 0 then [] else [(0, σ.symm 0)]
  first ++ (if (σ * swapsPerm first) 1 = 1 then [(1, 2)] else [])

/-- `toStd σ` brings every order `σ` to `(x, z, y)`. -/
theorem toStd_spec : ∀ σ : Equiv.Perm (Fin 3), σ * swapsPerm (toStd σ) = Equiv.swap 1 2 := by
  decide

/-- At most two swaps. -/
theorem toStd_length : ∀ σ : Equiv.Perm (Fin 3), (toStd σ).length ≤ 2 := by decide

/-- The complete reversible program for physical order `σ`: reorder to `(x, z, y)`, run the core,
and restore the order. -/
def prog (σ : Equiv.Perm (Fin 3)) : List Instr :=
  swapInstrs (toStd σ) ++ core ++ swapInstrs (toStd σ).reverse

/-- **The program implements `S₀`.** From every physical order `σ`, the program moves the record
with logical triple `v` to the record with logical triple `S₀ v`, in the same order `σ`. -/
theorem prog_spec (σ : Equiv.Perm (Fin 3)) (v : Tri L) :
    runProg L K ρ n (prog σ) (phys L σ v) = phys L σ (linesPerm L K ρ n lines v) := by
  rw [prog, runProg_append, runProg_append, runProg_swaps, toStd_spec, core_spec,
    runProg_swaps, swapsPerm_reverse, ← toStd_spec σ, mul_inv_cancel_right]

/-- Rotations in a program. -/
def Instr.isRot : Instr → Bool
  | .rot _ _ => true
  | .swap _ _ => false

/-- Exactly eight rotations and at most ten swaps. -/
theorem prog_counts : ∀ σ : Equiv.Perm (Fin 3),
    (prog σ).countP Instr.isRot = 8 ∧ (prog σ).countP (fun i => !i.isRot) ≤ 10 := by
  decide

end Program

/-! ### Record addresses and ranks -/

section Addresses

variable (N₀ N₁ N₂ N₃ L : ℕ)

/-- Spectator coordinates `(s₀, s₁, s₂, s₃) ∈ [N₀] × [N₁] × [N₂] × [N₃]`. -/
abbrev Spec := Fin N₀ × Fin N₁ × Fin N₂ × Fin N₃

/-- A record address: spectators and a triple of `L`-bit chunk values. As a logical address the
triple is indexed by the names `x = 0, y = 1, z = 2`; as a physical address by the slots. -/
abbrev Addr := Spec N₀ N₁ N₂ N₃ × Tri L

/-- Lexicographic rank of the physical address `(s₀, c₀, s₁, c₁, s₂, c₂, s₃)` in
`[N₀] × [2^L] × [N₁] × [2^L] × [N₂] × [2^L] × [N₃]`. -/
def rank (p : Addr N₀ N₁ N₂ N₃ L) : ℕ :=
  (p.1.2.2.2 : ℕ) + N₃ * ((p.2 2 : ℕ) + 2 ^ L * ((p.1.2.2.1 : ℕ) + N₂ * ((p.2 1 : ℕ) +
    2 ^ L * ((p.1.2.1 : ℕ) + N₁ * ((p.2 0 : ℕ) + 2 ^ L * (p.1.1 : ℕ))))))

/-- The rectangle size `M = N₀ N₁ N₂ N₃ 2^{3L}`, in left-to-right field order. -/
abbrev rectSize : ℕ := N₀ * 2 ^ L * N₁ * 2 ^ L * N₂ * 2 ^ L * N₃

/-- One more least significant coordinate. -/
def stepEquiv {α : Type*} {a : ℕ} (e : α ≃ Fin a) (b : ℕ) : α × Fin b ≃ Fin (a * b) :=
  (Equiv.prodCongr e (Equiv.refl _)).trans finProdFinEquiv

/-- The rank after adding a coordinate. -/
theorem stepEquiv_val {α : Type*} {a : ℕ} (e : α ≃ Fin a) (b : ℕ) (x : α) (y : Fin b) :
    (stepEquiv e b (x, y) : ℕ) = y + b * e x := by
  simp [stepEquiv, finProdFinEquiv]

/-- The seven physical coordinates as a left-nested product. -/
def nest : Addr N₀ N₁ N₂ N₃ L ≃
    ((((((Fin N₀ × Fin (2 ^ L)) × Fin N₁) × Fin (2 ^ L)) × Fin N₂) × Fin (2 ^ L)) × Fin N₃) where
  toFun p := ((((((p.1.1, p.2 0), p.1.2.1), p.2 1), p.1.2.2.1), p.2 2), p.1.2.2.2)
  invFun q := ((q.1.1.1.1.1.1, q.1.1.1.1.2, q.1.1.2, q.2), ![q.1.1.1.1.1.2, q.1.1.1.2, q.1.2])
  left_inv p := by
    obtain ⟨⟨s₀, s₁, s₂, s₃⟩, c⟩ := p
    simp only [Prod.mk.injEq, true_and]
    funext k
    fin_cases k <;> rfl
  right_inv q := rfl

/-- `nest` lists the coordinates `(s₀, c₀, s₁, c₁, s₂, c₂, s₃)`. -/
theorem nest_apply (p : Addr N₀ N₁ N₂ N₃ L) : nest N₀ N₁ N₂ N₃ L p =
    ((((((p.1.1, p.2 0), p.1.2.1), p.2 1), p.1.2.2.1), p.2 2), p.1.2.2.2) := rfl

/-- The rank bijection onto `[M]`. -/
def rankEquiv : Addr N₀ N₁ N₂ N₃ L ≃ Fin (rectSize N₀ N₁ N₂ N₃ L) :=
  (nest N₀ N₁ N₂ N₃ L).trans (stepEquiv (stepEquiv (stepEquiv (stepEquiv (stepEquiv
    (stepEquiv (Equiv.refl (Fin N₀)) (2 ^ L)) N₁) (2 ^ L)) N₂) (2 ^ L)) N₃)

/-- `rankEquiv` computes `rank`. -/
theorem rankEquiv_val (p : Addr N₀ N₁ N₂ N₃ L) :
    (rankEquiv N₀ N₁ N₂ N₃ L p : ℕ) = rank N₀ N₁ N₂ N₃ L p := by
  simp only [rankEquiv, Equiv.trans_apply, nest_apply, stepEquiv_val, Equiv.refl_apply, rank]

/-- The physical address of a logical address when slot `k` holds the name `σ k`. -/
def toPhys (σ : Equiv.Perm (Fin 3)) : Addr N₀ N₁ N₂ N₃ L ≃ Addr N₀ N₁ N₂ N₃ L :=
  Equiv.prodCongr (Equiv.refl _)
    { toFun := phys L σ
      invFun := phys L σ⁻¹
      left_inv := fun v => by funext k; simp [phys]
      right_inv := fun v => by funext k; simp [phys] }

/-- Address encoding for the stream in original order `σ`: logical address to rank. -/
def enc (σ : Equiv.Perm (Fin 3)) : Addr N₀ N₁ N₂ N₃ L ≃ Fin (rectSize N₀ N₁ N₂ N₃ L) :=
  (toPhys N₀ N₁ N₂ N₃ L σ).trans (rankEquiv N₀ N₁ N₂ N₃ L)

/-- The rank of a logical address in physical order `σ`. -/
theorem enc_val (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    (enc N₀ N₁ N₂ N₃ L σ a : ℕ) =
      rank N₀ N₁ N₂ N₃ L (a.1, phys L σ a.2) := rankEquiv_val _ _ _ _ _ _

/-- Lift a permutation of the triple to addresses, fixing the spectators. -/
def liftA (P : Equiv.Perm (Tri L)) : Equiv.Perm (Addr N₀ N₁ N₂ N₃ L) :=
  Equiv.prodCongr (Equiv.refl _) P

/-- A program acts on physical addresses through the chunk slots. -/
def runPhys (K ρ n : ℕ) (P : List Instr) (p : Addr N₀ N₁ N₂ N₃ L) : Addr N₀ N₁ N₂ N₃ L :=
  (p.1, runProg L K ρ n P p.2)

/-- On ranks: the record at rank `enc σ a` moves to rank `enc σ (S₀ a)`. -/
theorem prog_rank (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    rankEquiv N₀ N₁ N₂ N₃ L (runPhys N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ) (toPhys N₀ N₁ N₂ N₃ L σ a)) =
      enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a) := by
  simp only [enc, Equiv.trans_apply, runPhys, toPhys, liftA, Equiv.prodCongr_apply,
    Equiv.refl_apply, Prod.map, Equiv.coe_fn_mk, prog_spec, packedS]

end Addresses

/-! ### The exceptional set -/

section Guards

variable (K ρ n : ℕ)

/-- The guard value of segment `i`: the `K - 1` bits of `v` above the selected bit `ρ + i K`. -/
def guard (v i : ℕ) : ℕ := v / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1)

/-- The guard of segment `i` lies in `[m, 2^(K-1) - 1 - m]`. -/
def GuardOK (m v i : ℕ) : Prop := m ≤ guard K ρ v i ∧ guard K ρ v i + m < 2 ^ (K - 1)

instance (m v i : ℕ) : Decidable (GuardOK K ρ m v i) := by unfold GuardOK; infer_instance

/-- Good triples: all `2n` used guards (segments `i < n` of `y` and of `z`) are in range; the
packed program uses `n = f - 1`. -/
def Good (m : ℕ) {L : ℕ} (v : Tri L) : Prop :=
  ∀ i < n, GuardOK K ρ m (v 1) i ∧ GuardOK K ρ m (v 2) i

instance (m L : ℕ) : DecidablePred (Good K ρ n m (L := L)) := fun v => by
  unfold Good GuardOK; infer_instance

end Guards

section BadSet

variable (N₀ N₁ N₂ N₃ L K ρ f m : ℕ)

/-- **The exceptional set.** Some used guard (segment `i < f - 1` of `y` or of `z`) lies outside
`[m, 2^(K-1) - 1 - m]`. It reads only the chunk values `y` and `z`. -/
def Bad (a : Addr N₀ N₁ N₂ N₃ L) : Prop := ¬ Good K ρ (f - 1) m a.2

instance : DecidablePred (Bad N₀ N₁ N₂ N₃ L K ρ f m) := fun a => by
  unfold Bad; infer_instance

end BadSet

/-! ### Radix packing of segments -/

/-- Digit `i` of `digits B n t` is `⌊t / B^i⌋ mod B`. -/
theorem digits_getElem (B : ℤ) (hB : 0 ≤ B) (n : ℕ) (t : ℤ) (i : ℕ) (hi : i < n) :
    (digits B n t)[i]'(by rw [digits_length]; exact hi) = t / B ^ i % B := by
  induction n generalizing t i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [digits]
    | succ i =>
      simp only [digits, List.getElem_cons_succ]
      rw [ih (t / B) i (by omega), Int.ediv_ediv_of_nonneg hB, pow_succ']

/-- `digits` as an indexed list. -/
theorem digits_eq_range (B : ℤ) (hB : 0 ≤ B) (n : ℕ) (t : ℤ) :
    digits B n t = (List.range n).map (fun i => t / B ^ i % B) := by
  apply List.ext_getElem
  · simp [digits_length]
  · intro i h1 h2
    rw [digits_getElem B hB n t i (by rwa [digits_length] at h1)]
    simp

/-- The low `n` digits ignore multiples of `B^n`. -/
theorem digits_add_pow_mul (B : ℤ) (hB : 0 < B) (n : ℕ) (t s : ℤ) :
    digits B n (t + B ^ n * s) = digits B n t := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    simp only [digits]
    have h1 : t + B ^ (n + 1) * s = t + B * (B ^ n * s) := by ring
    rw [h1, Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ hB.ne', ih]

/-- Packing the low `n` digits gives the residue modulo `B^n`. -/
theorem pack_digits_mod (B : ℤ) (hB : 0 < B) (n : ℕ) (t : ℤ) :
    pack B (digits B n t) = t % B ^ n := by
  have ht : t = t % B ^ n + B ^ n * (t / B ^ n) := (Int.emod_add_mul_ediv t (B ^ n)).symm
  have hp : 0 < B ^ n := pow_pos hB n
  conv_lhs => rw [ht, digits_add_pow_mul B hB]
  exact pack_digits B hB n _ ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩

/-- `pack` is linear in a common factor. -/
theorem pack_range_map_mul (B c : ℤ) (n : ℕ) (d : ℕ → ℤ) :
    pack B ((List.range n).map (fun i => c * d i)) = c * pack B ((List.range n).map d) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, pack_append, pack_append, ih]
    simp [pack]
    ring

/-- `pack` of an indexed list is the radix sum. -/
theorem pack_range_eq_sum (B : ℤ) (n : ℕ) (d : ℕ → ℤ) :
    pack B ((List.range n).map d) = ∑ i ∈ Finset.range n, B ^ i * d i := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [List.range_succ, List.map_append, pack_append, ih, Finset.sum_range_succ]
    simp [pack]

/-- `pack` is additive on indexed lists. -/
theorem pack_range_add (B : ℤ) (n : ℕ) (d e : ℕ → ℤ) :
    pack B ((List.range n).map d) + pack B ((List.range n).map e) =
      pack B ((List.range n).map (fun i => d i + e i)) := by
  rw [pack_range_eq_sum, pack_range_eq_sum, pack_range_eq_sum, ← Finset.sum_add_distrib]
  simp [mul_add]

/-- An indexed list of digits in `[0, B)` is `Bounded`. -/
theorem bounded_range (B : ℤ) (n : ℕ) (d : ℕ → ℤ) (h : ∀ i < n, 0 ≤ d i ∧ d i < B) :
    Bounded B ((List.range n).map d) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i (List.mem_range.mp hi)

section Segments

variable (K ρ n : ℕ)

/-- Segment `i` of a field value: the `K` bits starting at the selected position `ρ + i K`. -/
def seg (v : ℤ) (i : ℕ) : ℤ := v / 2 ^ (ρ + i * K) % 2 ^ K

/-- The field value with low part `lo` (bits below `ρ`), segments `d 0, …, d (n-1)` and high
part `hi` (bits from `ρ + n K` on). -/
def assemble (lo hi : ℤ) (d : ℕ → ℤ) : ℤ :=
  lo + 2 ^ ρ * (pack (2 ^ K) ((List.range n).map d) + (2 ^ K) ^ n * hi)

/-- Range conditions for `assemble`. -/
def Fits (lo hi : ℤ) (d : ℕ → ℤ) : Prop :=
  (0 ≤ lo ∧ lo < 2 ^ ρ) ∧ (0 ≤ hi ∧ hi < 2 ^ (K - ρ)) ∧ ∀ i < n, 0 ≤ d i ∧ d i < 2 ^ K

/-- `2^L = 2^ρ · (2^K)^n · 2^{K - ρ}` for `L = (n + 1) K` and `ρ ≤ K`. -/
theorem pow_split (hρ : ρ ≤ K) :
    (2 : ℤ) ^ ((n + 1) * K) = 2 ^ ρ * (2 ^ K) ^ n * 2 ^ (K - ρ) := by
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  rw [Nat.add_mul, one_mul, Nat.mul_comm K n]
  omega

/-- Removing the low part of an assembled value. -/
theorem assemble_div (lo hi : ℤ) (d : ℕ → ℤ) (h : Fits K ρ n lo hi d) :
    assemble K ρ n lo hi d / 2 ^ ρ =
      pack (2 ^ K) ((List.range n).map d) + (2 ^ K) ^ n * hi := by
  unfold assemble
  have hp : (0 : ℤ) < 2 ^ ρ := by positivity
  rw [Int.add_mul_ediv_left _ _ hp.ne', Int.ediv_eq_zero_of_lt h.1.1 h.1.2, zero_add]

/-- The segments of an assembled value are its digits. -/
theorem digits_assemble (lo hi : ℤ) (d : ℕ → ℤ) (h : Fits K ρ n lo hi d) :
    digits (2 ^ K) n (assemble K ρ n lo hi d / 2 ^ ρ) = (List.range n).map d := by
  rw [assemble_div K ρ n lo hi d h, digits_add_pow_mul _ (by positivity)]
  have := digits_pack (2 ^ K) (by positivity) ((List.range n).map d)
    (bounded_range _ n d h.2.2)
  simpa using this

/-- Segment `i < n` of an assembled value is `d i`. -/
theorem seg_assemble (lo hi : ℤ) (d : ℕ → ℤ) (h : Fits K ρ n lo hi d) (i : ℕ) (hin : i < n) :
    seg K ρ (assemble K ρ n lo hi d) i = d i := by
  have h1 := congrArg (fun l => l[i]?) (digits_assemble K ρ n lo hi d h)
  simp only [digits_eq_range _ (by positivity : (0 : ℤ) ≤ 2 ^ K)] at h1
  simp only [List.getElem?_map, List.getElem?_range hin, Option.map_some, Option.some.injEq] at h1
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_mul, ← pow_add] at h1
  unfold seg
  rw [← h1, Nat.mul_comm K i]

/-- An assembled value with fitting parts is an `L`-bit value. -/
theorem assemble_bounds (hρ : ρ ≤ K) (lo hi : ℤ) (d : ℕ → ℤ) (h : Fits K ρ n lo hi d) :
    0 ≤ assemble K ρ n lo hi d ∧ assemble K ρ n lo hi d < 2 ^ ((n + 1) * K) := by
  obtain ⟨hlo, hhi, hd⟩ := h
  have hb := pack_bounds (2 ^ K) (by positivity) _ (bounded_range _ n d hd)
  rw [List.length_map, List.length_range] at hb
  have hρ' : (0 : ℤ) < 2 ^ ρ := by positivity
  have hQ : (0 : ℤ) < (2 ^ K) ^ n := by positivity
  have hm : 0 ≤ pack (2 ^ K) ((List.range n).map d) + (2 ^ K) ^ n * hi := by nlinarith
  have hm' : pack (2 ^ K) ((List.range n).map d) + (2 ^ K) ^ n * hi <
      (2 ^ K) ^ n * 2 ^ (K - ρ) := by nlinarith
  rw [pow_split K ρ n hρ]
  unfold assemble
  constructor <;> nlinarith

/-- Every nonnegative value is assembled from its own low part, segments and high part. -/
theorem decompose (v : ℤ) :
    v = assemble K ρ n (v % 2 ^ ρ) (v / 2 ^ ρ / (2 ^ K) ^ n) (seg K ρ v) := by
  have hQ : (0 : ℤ) < 2 ^ K := by positivity
  have h1 := pack_digits_mod (2 ^ K) hQ n (v / 2 ^ ρ)
  rw [digits_eq_range _ hQ.le] at h1
  have h2 : (List.range n).map (fun i => v / 2 ^ ρ / (2 ^ K) ^ i % 2 ^ K) =
      (List.range n).map (seg K ρ v) := by
    apply List.map_congr_left
    intro i _
    unfold seg
    rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_mul, ← pow_add, Nat.mul_comm K i]
  rw [h2] at h1
  unfold assemble
  rw [h1, Int.emod_add_mul_ediv, Int.emod_add_mul_ediv]

/-- The parts of an `L`-bit value fit. -/
theorem decompose_fits (hρ : ρ ≤ K) (v : ℤ) (hv : 0 ≤ v ∧ v < 2 ^ ((n + 1) * K)) :
    Fits K ρ n (v % 2 ^ ρ) (v / 2 ^ ρ / (2 ^ K) ^ n) (seg K ρ v) := by
  have hρ' : (0 : ℤ) < 2 ^ ρ := by positivity
  have hQ : (0 : ℤ) < 2 ^ K := by positivity
  have hQn : (0 : ℤ) < (2 ^ K) ^ n := by positivity
  refine ⟨⟨Int.emod_nonneg _ hρ'.ne', Int.emod_lt_of_pos _ hρ'⟩, ⟨?_, ?_⟩,
    fun i _ => ⟨Int.emod_nonneg _ hQ.ne', Int.emod_lt_of_pos _ hQ⟩⟩
  · exact Int.ediv_nonneg (Int.ediv_nonneg hv.1 hρ'.le) hQn.le
  · rw [Int.ediv_ediv_of_nonneg hρ'.le]
    apply (Int.ediv_lt_iff_lt_mul (by positivity)).mpr
    rw [pow_split K ρ n hρ] at hv
    linarith [hv.2]

/-- A rotation by a packed segment offset that keeps every segment in range acts segmentwise and
leaves the low and high parts unchanged. -/
theorem rotate_assemble (hρ : ρ ≤ K) (lo hi : ℤ) (d e : ℕ → ℤ) (h : Fits K ρ n lo hi d)
    (he : ∀ i < n, 0 ≤ d i + e i ∧ d i + e i < 2 ^ K) :
    (assemble K ρ n lo hi d + 2 ^ ρ * pack (2 ^ K) ((List.range n).map e)) %
        2 ^ ((n + 1) * K) = assemble K ρ n lo hi (fun i => d i + e i) := by
  obtain ⟨hlo, hhi, _⟩ := h
  have hb := pack_bounds (2 ^ K) (by positivity) _ (bounded_range _ n _ he)
  rw [List.length_map, List.length_range] at hb
  rw [pow_split K ρ n hρ]
  unfold assemble
  have := rotate_with_spectators (2 ^ ρ) ((2 ^ K) ^ n) (2 ^ (K - ρ)) lo
    (pack (2 ^ K) ((List.range n).map d)) hi (pack (2 ^ K) ((List.range n).map e))
    (by positivity) (by positivity) (by positivity) hlo hhi
    (by rw [pack_range_add]; exact hb)
  rw [this, pack_range_add]

end Segments

/-! ### One segment pair under the eight lines -/

/-- The digit-level test `[w ≡ b (mod 2)]` for a digit `w`. -/
def par (b : Bool) (r : ℤ) : ℤ := if b then r % 2 else 1 - r % 2

/-- A line on one segment pair `(u, w)` (segments of `y` and `z`) with control bit `c`. -/
def Line.dstep (l : Line) (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  if l.tgtY then (p.1 + sgn l.neg * (c * par l.b p.2), p.2)
  else (p.1, p.2 + sgn l.neg * (c * par l.b p.1))

/-- Run lines on one segment pair. -/
def runD (ls : List Line) (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := ls.foldl (fun p l => l.dstep c p) p

/-- Both entries of a segment pair are digits in `[0, Q)`. -/
def InR (Q : ℤ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 < Q ∧ 0 ≤ p.2 ∧ p.2 < Q

/-- Every intermediate segment pair of a run, including the start and the end, is in range. -/
def Safe (Q : ℤ) : List Line → ℤ → ℤ × ℤ → Prop
  | [], _, p => InR Q p
  | l :: ls, c, p => InR Q p ∧ Safe Q ls c (l.dstep c p)

/-- The start of a safe run is in range. -/
theorem Safe.inR {Q : ℤ} : ∀ {ls : List Line} {c : ℤ} {p : ℤ × ℤ}, Safe Q ls c p → InR Q p
  | [], _, _, h => h
  | _ :: _, _, _, h => h.1

/-- **The eight additions flip the parity of `u` exactly when `c = 1` and restore `w`.** -/
theorem runD_lines (c u w : ℤ) (hc : c = 0 ∨ c = 1) :
    runD lines c (u, w) = (toggle u c, w) := by
  rcases hc with rfl | rfl <;>
  simp only [runD, lines, List.foldl_cons, List.foldl_nil, Line.dstep, sgn, par, toggle,
    ite_true, ite_false, Bool.false_eq_true, Prod.mk.injEq] <;>
  constructor <;> omega

/-- With `2 ≤ u, w` and `u, w ≤ Q - 3` (guard margin at least one), all intermediate pairs
stay in `[0, Q)`. -/
theorem safe_lines (Q c u w : ℤ) (hc : c = 0 ∨ c = 1) (hu : 2 ≤ u ∧ u + 3 ≤ Q)
    (hw : 2 ≤ w ∧ w + 3 ≤ Q) : Safe Q lines c (u, w) := by
  rcases hc with rfl | rfl <;>
  simp only [Safe, lines, Line.dstep, sgn, par, InR,
    ite_true, ite_false, Bool.false_eq_true] <;>
  omega

/-! ### Packed lines act segmentwise on guarded addresses -/

section Bits

variable (K ρ n : ℕ)

/-- The control bit `x_{j_i}` as an integer. -/
def cbit (x i : ℕ) : ℤ := if x.testBit (ρ + i * K) then 1 else 0

/-- Control bits are `0` or `1`. -/
theorem cbit_bit (x i : ℕ) : cbit K ρ x i = 0 ∨ cbit K ρ x i = 1 := by
  unfold cbit; split <;> simp

/-- The selected bit `j_i` of an assembled value is the parity of its segment `i`. -/
theorem testBit_assemble (hK : 1 ≤ K) (v : ℕ) (lo hi : ℤ) (d : ℕ → ℤ)
    (hv : (v : ℤ) = assemble K ρ n lo hi d) (h : Fits K ρ n lo hi d) (i : ℕ) (hin : i < n) :
    v.testBit (ρ + i * K) = decide (d i % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 := seg_assemble K ρ n lo hi d h i hin
  rw [← hv] at h1
  unfold seg at h1
  have h2 : (2 : ℤ) ∣ 2 ^ K := dvd_pow_self 2 (by omega)
  have h3 : ((v / 2 ^ (ρ + i * K) % 2 : ℕ) : ℤ) = d i % 2 := by
    rw [← h1, Int.emod_emod_of_dvd _ h2]; push_cast; rfl
  simp only [decide_eq_decide]
  omega

/-- The packed offset as `2^ρ` times a packed list of segment increments. -/
theorem offMag_eq (b : Bool) (c w : ℕ) :
    (offMag K ρ n b c w : ℤ) = 2 ^ ρ * pack (2 ^ K) ((List.range n).map (fun i =>
      if c.testBit (ρ + i * K) = true ∧ w.testBit (ρ + i * K) = b then 1 else 0)) := by
  rw [pack_range_eq_sum, Finset.mul_sum]
  unfold offMag
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · simp only [mul_one, pow_add, ← pow_mul, Nat.mul_comm i K]
  · simp

/-- The selected-bit indicator of `offMag` in terms of the control bit and segment parity. -/
theorem ind_eq (hK : 1 ≤ K) (b : Bool) (c w : ℕ) (lo hi : ℤ) (d : ℕ → ℤ)
    (hw : (w : ℤ) = assemble K ρ n lo hi d) (h : Fits K ρ n lo hi d) (i : ℕ) (hin : i < n) :
    (if c.testBit (ρ + i * K) = true ∧ w.testBit (ρ + i * K) = b then (1 : ℤ) else 0) =
      cbit K ρ c i * par b (d i) := by
  rw [testBit_assemble K ρ n hK w lo hi d hw h i hin]
  have h2 : d i % 2 = 0 ∨ d i % 2 = 1 := by omega
  unfold cbit par
  cases b <;> by_cases hc : c.testBit (ρ + i * K) = true <;> rcases h2 with h2 | h2 <;>
    simp [hc, h2]

/-- `assemble` reads only the segments `i < n`. -/
theorem assemble_congr (lo hi : ℤ) (d d' : ℕ → ℤ) (h : ∀ i < n, d i = d' i) :
    assemble K ρ n lo hi d = assemble K ρ n lo hi d' := by
  have hm : (List.range n).map d = (List.range n).map d' :=
    List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))
  unfold assemble
  rw [hm]

/-- One packed rotation of target `t` by `± offMag b x w` acts on every segment as the digit
update `d_i ← d_i ± c_i [w_i ≡ b]`, provided all new digits stay in range. -/
theorem rot_line (hρ : ρ < K) (L : ℕ) (hL : L = (n + 1) * K) (neg b : Bool)
    (x t w : Fin (2 ^ L)) (lo hi lo' hi' : ℤ) (d d' : ℕ → ℤ)
    (ht : ((t : ℕ) : ℤ) = assemble K ρ n lo hi d)
    (hw : ((w : ℕ) : ℤ) = assemble K ρ n lo' hi' d')
    (hf : Fits K ρ n lo hi d) (hf' : Fits K ρ n lo' hi' d')
    (hout : ∀ i < n, 0 ≤ d i + sgn neg * (cbit K ρ x i * par b (d' i)) ∧
      d i + sgn neg * (cbit K ρ x i * par b (d' i)) < 2 ^ K) :
    (((rot L t (sgn neg * offMag K ρ n b x w) : Fin (2 ^ L)) : ℕ) : ℤ) =
      assemble K ρ n lo hi (fun i => d i + sgn neg * (cbit K ρ x i * par b (d' i))) := by
  subst hL
  have hK : 1 ≤ K := by omega
  have hmap : (List.range n).map (fun i => sgn neg *
      (if (x : ℕ).testBit (ρ + i * K) = true ∧ (w : ℕ).testBit (ρ + i * K) = b
        then (1 : ℤ) else 0)) =
      (List.range n).map (fun i => sgn neg * (cbit K ρ x i * par b (d' i))) := by
    apply List.map_congr_left
    intro i hi
    rw [ind_eq K ρ n hK b x w lo' hi' d' hw hf' i (List.mem_range.mp hi)]
  rw [rot_val, ht, offMag_eq, show (sgn neg : ℤ) * (2 ^ ρ * pack (2 ^ K) ((List.range n).map
      (fun i => if (x : ℕ).testBit (ρ + i * K) = true ∧ (w : ℕ).testBit (ρ + i * K) = b
        then (1 : ℤ) else 0))) =
      2 ^ ρ * pack (2 ^ K) ((List.range n).map (fun i => sgn neg *
      (if (x : ℕ).testBit (ρ + i * K) = true ∧ (w : ℕ).testBit (ρ + i * K) = b
        then (1 : ℤ) else 0))) by rw [pack_range_map_mul]; ring, hmap]
  exact rotate_assemble K ρ n hρ.le lo hi d _ hf hout

end Bits

section Run

variable (K ρ n : ℕ)

/-- One line on assembled values acts on every segment pair as `Line.dstep`, provided the new
digits are in range. -/
theorem line_step (hρ : ρ < K) (L : ℕ) (hL : L = (n + 1) * K) (l : Line) (v : Tri L)
    (p : ℕ → ℤ × ℤ) (loY hiY loZ hiZ : ℤ)
    (hy : ((v 1 : ℕ) : ℤ) = assemble K ρ n loY hiY (fun i => (p i).1))
    (hz : ((v 2 : ℕ) : ℤ) = assemble K ρ n loZ hiZ (fun i => (p i).2))
    (hfy : Fits K ρ n loY hiY (fun i => (p i).1)) (hfz : Fits K ρ n loZ hiZ (fun i => (p i).2))
    (hout : ∀ i < n, InR (2 ^ K) (l.dstep (cbit K ρ (v 0) i) (p i))) :
    (l.perm L K ρ n v) 0 = v 0 ∧
    (((l.perm L K ρ n v) 1 : ℕ) : ℤ) =
      assemble K ρ n loY hiY (fun i => (l.dstep (cbit K ρ (v 0) i) (p i)).1) ∧
    (((l.perm L K ρ n v) 2 : ℕ) : ℤ) =
      assemble K ρ n loZ hiZ (fun i => (l.dstep (cbit K ρ (v 0) i) (p i)).2) := by
  obtain ⟨tgtY, neg, b⟩ := l
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  cases tgtY
  · simp only [Line.perm, crotPerm, Equiv.coe_fn_mk, crot, Line.tgt, Line.oth,
      Bool.false_eq_true, ite_false, Line.dstep, Line.offset]
    refine ⟨Function.update_of_ne h20.symm _ _, ?_, ?_⟩
    · rw [Function.update_of_ne h12]; exact hy
    · rw [Function.update_self]
      exact rot_line K ρ n hρ L hL neg b (v 0) (v 2) (v 1) loZ hiZ loY hiY _ _ hz hy hfz hfy
        (fun i hi => ⟨(hout i hi).2.2.1, (hout i hi).2.2.2⟩)
  · simp only [Line.perm, crotPerm, Equiv.coe_fn_mk, crot, Line.tgt, Line.oth,
      ite_true, Line.dstep, Line.offset]
    refine ⟨Function.update_of_ne h10.symm _ _, ?_, ?_⟩
    · rw [Function.update_self]
      exact rot_line K ρ n hρ L hL neg b (v 0) (v 1) (v 2) loY hiY loZ hiZ _ _ hy hz hfy hfz
        (fun i hi => ⟨(hout i hi).1, (hout i hi).2.1⟩)
    · rw [Function.update_of_ne h12.symm]; exact hz

/-- Range data for the `y` and `z` parts from in-range segment pairs. -/
theorem fits_of_inR (lo hi : ℤ) (p : ℕ → ℤ × ℤ) (hlo : 0 ≤ lo ∧ lo < 2 ^ ρ)
    (hhi : 0 ≤ hi ∧ hi < 2 ^ (K - ρ)) (h : ∀ i < n, InR (2 ^ K) (p i)) :
    Fits K ρ n lo hi (fun i => (p i).1) ∧ Fits K ρ n lo hi (fun i => (p i).2) :=
  ⟨⟨hlo, hhi, fun i hi => ⟨(h i hi).1, (h i hi).2.1⟩⟩,
   ⟨hlo, hhi, fun i hi => ⟨(h i hi).2.2.1, (h i hi).2.2.2⟩⟩⟩

/-- **Packed lines act segmentwise.** If all intermediate digits of every segment pair stay in
range, the packed run of the lines acts on `y` and `z` as the digit-level run on every segment,
and it fixes `x` and the low and high parts. -/
theorem run_lines (hρ : ρ < K) (L : ℕ) (hL : L = (n + 1) * K) (loY hiY loZ hiZ : ℤ)
    (hloY : 0 ≤ loY ∧ loY < 2 ^ ρ) (hhiY : 0 ≤ hiY ∧ hiY < 2 ^ (K - ρ))
    (hloZ : 0 ≤ loZ ∧ loZ < 2 ^ ρ) (hhiZ : 0 ≤ hiZ ∧ hiZ < 2 ^ (K - ρ)) :
    ∀ (ls : List Line) (v : Tri L) (p : ℕ → ℤ × ℤ),
    ((v 1 : ℕ) : ℤ) = assemble K ρ n loY hiY (fun i => (p i).1) →
    ((v 2 : ℕ) : ℤ) = assemble K ρ n loZ hiZ (fun i => (p i).2) →
    (∀ i < n, Safe (2 ^ K) ls (cbit K ρ (v 0) i) (p i)) →
    (linesPerm L K ρ n ls v) 0 = v 0 ∧
    (((linesPerm L K ρ n ls v) 1 : ℕ) : ℤ) =
      assemble K ρ n loY hiY (fun i => (runD ls (cbit K ρ (v 0) i) (p i)).1) ∧
    (((linesPerm L K ρ n ls v) 2 : ℕ) : ℤ) =
      assemble K ρ n loZ hiZ (fun i => (runD ls (cbit K ρ (v 0) i) (p i)).2)
  | [], v, p, hy, hz, _ => ⟨rfl, hy, hz⟩
  | l :: ls, v, p, hy, hz, hs => by
    have hin : ∀ i < n, InR (2 ^ K) (p i) := fun i hi => (hs i hi).1
    have hout : ∀ i < n, InR (2 ^ K) (l.dstep (cbit K ρ (v 0) i) (p i)) :=
      fun i hi => (hs i hi).2.inR
    obtain ⟨hfy, hfz⟩ := fits_of_inR K ρ n loY hiY p hloY hhiY hin
    obtain ⟨hfy', hfz'⟩ := fits_of_inR K ρ n loZ hiZ p hloZ hhiZ hin
    obtain ⟨h0, h1, h2⟩ := line_step K ρ n hρ L hL l v p loY hiY loZ hiZ hy hz hfy hfz' hout
    have ih := run_lines hρ L hL loY hiY loZ hiZ hloY hhiY hloZ hhiZ ls (l.perm L K ρ n v)
      (fun i => l.dstep (cbit K ρ (v 0) i) (p i)) h1 h2 (by
        intro i hi; rw [h0]; exact (hs i hi).2)
    rw [h0] at ih
    exact ih

end Run

/-! ### The ideal map on segments, and agreement -/

section Ideal

variable (K ρ n : ℕ)

/-- Bits of `selMask` outside the selected positions vanish. -/
theorem selMask_false {j : ℕ} (h : ¬ IsSel K ρ n j) : (selMask K ρ n).testBit j = false := by
  rw [Bool.eq_false_iff, ne_eq, testBit_selMask]; exact h

/-- Bits of a one-bit value. -/
theorem testBit_bit (c : Bool) (t : ℕ) :
    (if c = true then 1 else 0 : ℕ).testBit t = (c && decide (t = 0)) := by
  cases c
  · simp
  · simp only [ite_true, Bool.true_and]
    rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]

/-- Two selected positions never differ by `t ∈ (0, K)`. -/
theorem sel_ne {i i' t : ℕ} (ht0 : 0 < t) (htK : t < K) :
    ρ + i' * K ≠ ρ + i * K + t := by
  intro h
  rcases le_or_gt i' i with h1 | h1
  · have := Nat.mul_le_mul_right K h1; omega
  · have := Nat.mul_le_mul_right K (show i + 1 ≤ i' by omega)
    rw [Nat.add_mul, one_mul] at this; omega

/-- Within segment `i`, only its lowest bit is selected. -/
theorem isSel_seg {i t : ℕ} (hin : i < n) (ht : t < K) :
    IsSel K ρ n (t + (ρ + i * K)) ↔ t = 0 := by
  constructor
  · rintro ⟨i', _, h⟩
    by_contra h0
    exact sel_ne K ρ (i := i) (i' := i') (Nat.pos_of_ne_zero h0) ht (by omega)
  · rintro rfl; exact ⟨i, hin, by omega⟩

/-- No position below `ρ` is selected. -/
theorem not_isSel_lo {t : ℕ} (ht : t < ρ) : ¬ IsSel K ρ n t := by
  rintro ⟨i', _, h⟩; omega

/-- No position from `ρ + n K` on is among the first `n` selected positions. -/
theorem not_isSel_hi (hK : 1 ≤ K) (t : ℕ) : ¬ IsSel K ρ n (t + (ρ + n * K)) := by
  rintro ⟨i', hi', h⟩
  have := Nat.mul_le_mul_right K (show i' + 1 ≤ n by omega)
  rw [Nat.add_mul, one_mul] at this; omega

/-- The guard bits of a segment are not selected. -/
theorem not_isSel_guard (hK : 1 ≤ K) {i t : ℕ} (ht : t < K - 1) :
    ¬ IsSel K ρ n (t + (ρ + i * K + 1)) := by
  rintro ⟨i', _, h⟩
  exact sel_ne K ρ (i := i) (i' := i') (t := t + 1) (by omega) (by omega) (by omega)

/-- The ideal XOR fixes the low part. -/
theorem xor_lo (x y : ℕ) : (y ^^^ (x &&& selMask K ρ n)) % 2 ^ ρ = y % 2 ^ ρ := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_and]
  by_cases ht : t < ρ
  · simp [ht, selMask_false K ρ n (not_isSel_lo K ρ n ht)]
  · simp [ht]

/-- The ideal XOR fixes the high part. -/
theorem xor_hi (hK : 1 ≤ K) (x y : ℕ) :
    (y ^^^ (x &&& selMask K ρ n)) / 2 ^ (ρ + n * K) = y / 2 ^ (ρ + n * K) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp [Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_and,
    selMask_false K ρ n (not_isSel_hi K ρ n hK t)]

/-- The ideal XOR flips bit `0` of segment `i` exactly when `x_{j_i} = 1`. -/
theorem xor_seg (hK : 1 ≤ K) (x y : ℕ) {i : ℕ} (hin : i < n) :
    (y ^^^ (x &&& selMask K ρ n)) / 2 ^ (ρ + i * K) % 2 ^ K =
      (y / 2 ^ (ρ + i * K) % 2 ^ K) ^^^ (if x.testBit (ρ + i * K) then 1 else 0) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor,
    Nat.testBit_and, testBit_bit]
  by_cases ht : t < K
  · by_cases h0 : t = 0
    · subst h0
      have hs : (selMask K ρ n).testBit (ρ + i * K) = true := by
        have := (testBit_selMask K ρ n (0 + (ρ + i * K))).mpr ((isSel_seg K ρ n hin ht).mpr rfl)
        simpa using this
      simp [hs, ht]
    · have hs := selMask_false K ρ n (mt (isSel_seg K ρ n hin ht).mp h0)
      simp [ht, h0, hs]
  · simp [ht]
    omega

/-- The ideal XOR fixes every guard value. -/
theorem xor_guard (hK : 1 ≤ K) (x y : ℕ) (i : ℕ) :
    (y ^^^ (x &&& selMask K ρ n)) / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) =
      y / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor,
    Nat.testBit_and]
  by_cases ht : t < K - 1
  · simp [ht, selMask_false K ρ n (not_isSel_guard K ρ n hK (i := i) ht)]
  · simp [ht]

/-- XOR with a bit is `toggle`. -/
theorem natCast_xor_bit (d : ℕ) (c : Bool) :
    (((d ^^^ (if c = true then 1 else 0) : ℕ)) : ℤ) = toggle d (if c = true then 1 else 0) := by
  cases c
  · simp [toggle]
  · simp only [ite_true, toggle]
    rcases Nat.even_or_odd d with h | h
    · rw [Nat.xor_one_of_even h]
      have := Nat.even_iff.mp h
      omega
    · rw [Nat.xor_one_of_odd h]
      have := Nat.odd_iff.mp h
      omega

/-- The `y` value of the ideal map, assembled from toggled segments. -/
theorem idealT_rep (hρ : ρ < K) (L : ℕ) (v : Tri L) :
    ((((xorMask L (selMask K ρ n) v) 1 : Fin (2 ^ L)) : ℕ) : ℤ) =
      assemble K ρ n (((v 1 : ℕ) : ℤ) % 2 ^ ρ) (((v 1 : ℕ) : ℤ) / 2 ^ ρ / (2 ^ K) ^ n)
        (fun i => toggle (seg K ρ ((v 1 : ℕ) : ℤ) i) (cbit K ρ (v 0) i)) := by
  have hK : 1 ≤ K := by omega
  simp only [xorMask, Function.update_self]
  generalize ((v 1 : ℕ)) = y
  generalize ((v 0 : ℕ)) = x
  rw [decompose K ρ n (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ)]
  have h1 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) % 2 ^ ρ = (y : ℤ) % 2 ^ ρ := by
    exact_mod_cast xor_lo K ρ n x y
  have h2 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) / 2 ^ ρ / (2 ^ K) ^ n =
      (y : ℤ) / 2 ^ ρ / (2 ^ K) ^ n := by
    rw [Int.ediv_ediv_of_nonneg (by positivity), Int.ediv_ediv_of_nonneg (by positivity),
      ← pow_mul, ← pow_add, Nat.mul_comm K n]
    exact_mod_cast xor_hi K ρ n hK x y
  rw [h1, h2]
  apply assemble_congr
  intro i hi
  unfold seg cbit
  have h3 := xor_seg K ρ n hK x y hi
  have h4 : (((y ^^^ (x &&& selMask K ρ n) : ℕ)) : ℤ) / 2 ^ (ρ + i * K) % 2 ^ K =
      (((y ^^^ (x &&& selMask K ρ n)) / 2 ^ (ρ + i * K) % 2 ^ K : ℕ) : ℤ) := by
    push_cast; rfl
  have h5 : (y : ℤ) / 2 ^ (ρ + i * K) % 2 ^ K = ((y / 2 ^ (ρ + i * K) % 2 ^ K : ℕ) : ℤ) := by
    push_cast; rfl
  rw [h4, h3, natCast_xor_bit, h5]

/-- The guard value is half the segment. -/
theorem seg_half (hK : 1 ≤ K) (y i : ℕ) : seg K ρ (y : ℤ) i / 2 = (guard K ρ y i : ℤ) := by
  unfold seg guard
  have h : (y / 2 ^ (ρ + i * K) % 2 ^ K / 2 : ℕ) = y / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) := by
    rw [show 2 ^ K = 2 * 2 ^ (K - 1) by rw [← pow_succ']; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_succ]
  rw [← h]
  push_cast
  rfl

/-- A guard in range with margin at least one gives `2 ≤ seg ≤ 2^K - 3`. -/
theorem seg_bounds_of_guard (hK : 1 ≤ K) (m : ℕ) (hm : 1 ≤ m) (y i : ℕ)
    (h : GuardOK K ρ m y i) : 2 ≤ seg K ρ (y : ℤ) i ∧ seg K ρ (y : ℤ) i + 3 ≤ 2 ^ K := by
  have h1 := seg_half K ρ hK y i
  have h2 : 0 ≤ seg K ρ (y : ℤ) i := Int.emod_nonneg _ (by positivity)
  have h3 : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨g1, g2⟩ := h
  have g2' : ((guard K ρ y i : ℕ) : ℤ) + m < (2 : ℤ) ^ (K - 1) := by exact_mod_cast g2
  omega

/-- The ideal map preserves the good set. -/
theorem good_idealT (hK : 1 ≤ K) (m L : ℕ) (v : Tri L) :
    Good K ρ n m (xorMask L (selMask K ρ n) v) ↔ Good K ρ n m v := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hg : ∀ i, guard K ρ (((xorMask L (selMask K ρ n) v) 1 : Fin (2 ^ L)) : ℕ) i =
      guard K ρ (v 1 : ℕ) i := by
    intro i
    simp only [xorMask, Function.update_self]
    exact xor_guard K ρ n hK _ _ i
  have hz : (xorMask L (selMask K ρ n) v) 2 = v 2 := by
    simp only [xorMask, Function.update_of_ne h21]
  simp only [Good, GuardOK, hg, hz]

/-- **Agreement off the exceptional set.** On every good triple, the eight packed lines equal
the ideal XOR at the first `n = f - 1` selected positions. -/
theorem lines_agree (hρ : ρ < K) (L : ℕ) (hL : L = (n + 1) * K) (m : ℕ) (hm : 1 ≤ m)
    (v : Tri L) (hv : Good K ρ n m v) :
    linesPerm L K ρ n lines v = xorMask L (selMask K ρ n) v := by
  have hK : 1 ≤ K := by omega
  set y : ℤ := ((v 1 : ℕ) : ℤ) with hydef
  set z : ℤ := ((v 2 : ℕ) : ℤ) with hzdef
  have hy0 : 0 ≤ y ∧ y < 2 ^ ((n + 1) * K) := by
    have : ((v 1 : ℕ)) < 2 ^ ((n + 1) * K) :=
      calc ((v 1 : ℕ)) < 2 ^ L := (v 1).isLt
        _ = 2 ^ ((n + 1) * K) := by rw [hL]
    exact ⟨by positivity, by simp only [hydef]; exact_mod_cast this⟩
  have hz0 : 0 ≤ z ∧ z < 2 ^ ((n + 1) * K) := by
    have : ((v 2 : ℕ)) < 2 ^ ((n + 1) * K) :=
      calc ((v 2 : ℕ)) < 2 ^ L := (v 2).isLt
        _ = 2 ^ ((n + 1) * K) := by rw [hL]
    exact ⟨by positivity, by simp only [hzdef]; exact_mod_cast this⟩
  have fy := decompose_fits K ρ n hρ.le y hy0
  have fz := decompose_fits K ρ n hρ.le z hz0
  let p : ℕ → ℤ × ℤ := fun i => (seg K ρ y i, seg K ρ z i)
  have hsafe : ∀ i < n, Safe (2 ^ K) lines (cbit K ρ (v 0) i) (p i) := by
    intro i hi
    exact safe_lines _ _ _ _ (cbit_bit K ρ _ i)
      (seg_bounds_of_guard K ρ hK m hm _ i (hv i hi).1)
      (seg_bounds_of_guard K ρ hK m hm _ i (hv i hi).2)
  obtain ⟨r0, r1, r2⟩ := run_lines K ρ n hρ L hL _ _ _ _ fy.1 fy.2.1 fz.1 fz.2.1 lines v p
    (decompose K ρ n y) (decompose K ρ n z) hsafe
  have hrun : ∀ i < n, runD lines (cbit K ρ (v 0) i) (p i) =
      (toggle (seg K ρ y i) (cbit K ρ (v 0) i), seg K ρ z i) :=
    fun i _ => runD_lines _ _ _ (cbit_bit K ρ _ i)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  funext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, r0, xorMask, Function.update_of_ne h01]
  · apply Fin.ext
    apply Int.ofNat.inj
    change (((linesPerm L K ρ n lines v) 1 : ℕ) : ℤ) =
      ((((xorMask L (selMask K ρ n) v) 1 : Fin (2 ^ L)) : ℕ) : ℤ)
    rw [r1, idealT_rep K ρ n hρ L v]
    exact assemble_congr K ρ n _ _ _ _ (fun i hi => by rw [hrun i hi])
  · apply Fin.ext
    apply Int.ofNat.inj
    change (((linesPerm L K ρ n lines v) 2 : ℕ) : ℤ) =
      ((((xorMask L (selMask K ρ n) v) 2 : Fin (2 ^ L)) : ℕ) : ℤ)
    rw [r2, xorMask, Function.update_of_ne h21]
    rw [assemble_congr K ρ n _ _ _ (fun i => seg K ρ z i) (fun i hi => by rw [hrun i hi])]
    exact (decompose K ρ n z).symm

end Ideal

/-! ### Repair and the top fixup -/

section Repair

variable (N₀ N₁ N₂ N₃ L K ρ f m : ℕ)

/-- The ideal map preserves `Bad`. -/
theorem idealT_preserves_bad (hK : 1 ≤ K) (a : Addr N₀ N₁ N₂ N₃ L) :
    Bad N₀ N₁ N₂ N₃ L K ρ f m (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) a) ↔
      Bad N₀ N₁ N₂ N₃ L K ρ f m a :=
  not_congr (good_idealT K ρ (f - 1) hK m L a.2)

/-- **Agreement off the exceptional set**, on record addresses. -/
theorem packed_agrees (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (a : Addr N₀ N₁ N₂ N₃ L) (ha : ¬ Bad N₀ N₁ N₂ N₃ L K ρ f m a) :
    liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a = liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) a := by
  have hL' : L = (f - 1 + 1) * K := by rw [hL, Nat.sub_add_cancel hf]
  exact Prod.ext rfl (lines_agree K ρ (f - 1) hρ L hL' m hm a.2 (not_not.mp ha))

/-- The packed program preserves `Bad` (from the vendored `actual_preserves_bad`). -/
theorem packed_preserves_bad (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (a : Addr N₀ N₁ N₂ N₃ L) :
    Bad N₀ N₁ N₂ N₃ L K ρ f m (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a) ↔
      Bad N₀ N₁ N₂ N₃ L K ρ f m a :=
  actual_preserves_bad _ _ _ (idealT_preserves_bad N₀ N₁ N₂ N₃ L K ρ f m (by omega))
    (packed_agrees N₀ N₁ N₂ N₃ L K ρ f m hρ hL hf hm) a

/-- **Exceptional repair.** The vendored extract–sort–fill pipeline, run on the stream after the
packed program, yields the stream of the ideal map `idealT` everywhere. -/
theorem repair_exact (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (σ : Equiv.Perm (Fin 3)) (k : ℕ) (hk : rectSize N₀ N₁ N₂ N₃ L ≤ 2 ^ k)
    (data : Addr N₀ N₁ N₂ N₃ L → List Bool) :
    pipeline (enc N₀ N₁ N₂ N₃ L σ) (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f))
        (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f)) (Bad N₀ N₁ N₂ N₃ L K ρ f m) k data =
      stream (enc N₀ N₁ N₂ N₃ L σ) (Bad N₀ N₁ N₂ N₃ L K ρ f m)
        (data ∘ (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f)).symm) :=
  pipeline_exact _ _ _ _ (idealT_preserves_bad N₀ N₁ N₂ N₃ L K ρ f m (by omega))
    (packed_agrees N₀ N₁ N₂ N₃ L K ρ f m hρ hL hf hm) k hk data

end Repair

section Fixup

variable (L K ρ f : ℕ)

/-- `xorSel = topFix ∘ idealT`: the packed lines handle `j_0, …, j_{f-2}` and the fixup handles
`j_{f-1}`. -/
theorem xorSel_eq (hK : 1 ≤ K) (hf : 1 ≤ f) :
    xorSel L K ρ f = topFix L K ρ f * idealT L K ρ f := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  ext v k
  simp only [Equiv.Perm.mul_apply]
  change ((xorMask L (selMask K ρ (n + 1)) v) k : ℕ) =
    ((xorMask L (2 ^ (ρ + n * K)) (xorMask L (selMask K ρ n) v)) k : ℕ)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  by_cases hk : k = 1
  · subst hk
    simp only [xorMask, Function.update_self, Function.update_of_ne h01]
    apply Nat.eq_of_testBit_eq
    intro t
    have hdis : (selMask K ρ n).testBit t = true → (2 ^ (ρ + n * K) : ℕ).testBit t = false := by
      intro h
      rw [testBit_selMask] at h
      rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
      rintro rfl
      exact not_isSel_hi K ρ n hK 0 (by simpa using h)
    simp only [selMask, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
    cases h1 : (selMask K ρ n).testBit t <;> cases h2 : (2 ^ (ρ + n * K) : ℕ).testBit t <;>
      simp_all
  · simp only [xorMask, Function.update_of_ne hk]

end Fixup

section FixupAddr

variable (N₀ N₁ N₂ N₃ L K ρ f : ℕ)

/-- **Top fixup.** After the repair, the two-bit XOR at `j_{f-1}` completes the target. -/
theorem fixup_after_repair (hK : 1 ≤ K) (hf : 1 ≤ f) {β : Type*} (data : Addr N₀ N₁ N₂ N₃ L → β) :
    (data ∘ (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f)).symm) ∘
        (liftA N₀ N₁ N₂ N₃ L (topFix L K ρ f)).symm =
      data ∘ (liftA N₀ N₁ N₂ N₃ L (xorSel L K ρ f)).symm := by
  rw [xorSel_eq L K ρ f hK hf]
  rfl

end FixupAddr

/-! ### Counting exceptional addresses -/

section Density

/-- At most `2m` guard values of `[0, 2^t)` lie outside `[m, 2^t - 1 - m]`. -/
theorem card_E (m t : ℕ) :
    Fintype.card {g : Fin (2 ^ t) // ¬ (m ≤ (g : ℕ) ∧ (g : ℕ) + m < 2 ^ t)} ≤ 2 * m := by
  have h := Fintype.card_le_of_injective (β := Fin (2 * m))
    (fun g : {g : Fin (2 ^ t) // ¬ (m ≤ (g : ℕ) ∧ (g : ℕ) + m < 2 ^ t)} =>
      ⟨if (g.1 : ℕ) < m then g.1 else m + (2 ^ t - 1 - g.1), by
      have := g.1.isLt; have := g.2; split_ifs <;> omega⟩)
    (by
      intro g h e
      simp only [Fin.mk.injEq] at e
      apply Subtype.ext; apply Fin.ext
      have := g.1.isLt; have := h.1.isLt; have := g.2; have := h.2
      split_ifs at e <;> omega)
  simpa using h

variable (K ρ L : ℕ)

/-- One guard fails on at most `2m · 2^{L - (K-1)}` values of an `L`-bit chunk. -/
theorem card_guard_fail (hK : 1 ≤ K) (m i : ℕ) (hi : ρ + (i + 1) * K ≤ L) :
    Fintype.card {y : Fin (2 ^ L) // ¬ GuardOK K ρ m y i} ≤ 2 * m * 2 ^ (L - (K - 1)) := by
  have hst : ρ + i * K + 1 + (K - 1) ≤ L := by rw [Nat.add_mul, one_mul] at hi; omega
  let F : {y : Fin (2 ^ L) // ¬ GuardOK K ρ m y i} →
      Fin (2 ^ (ρ + i * K + 1)) × {g : Fin (2 ^ (K - 1)) // ¬ (m ≤ (g : ℕ) ∧ (g : ℕ) + m < 2 ^ (K - 1))} ×
        Fin (2 ^ (L - (ρ + i * K + 1 + (K - 1)))) := fun y =>
    (⟨y.1 % 2 ^ (ρ + i * K + 1), Nat.mod_lt _ (by positivity)⟩,
     ⟨⟨y.1 / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1), Nat.mod_lt _ (by positivity)⟩, y.2⟩,
     ⟨y.1 / 2 ^ (ρ + i * K + 1 + (K - 1)), by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
        calc (y.1 : ℕ) < 2 ^ L := y.1.isLt
          _ = 2 ^ (L - (ρ + i * K + 1 + (K - 1)) + (ρ + i * K + 1 + (K - 1))) := by
            congr 1; omega⟩)
  have key : ∀ y : ℕ, y = y % 2 ^ (ρ + i * K + 1) + 2 ^ (ρ + i * K + 1) *
      (y / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) + 2 ^ (K - 1) * (y / 2 ^ (ρ + i * K + 1 + (K - 1)))) := by
    intro y
    rw [show 2 ^ (ρ + i * K + 1 + (K - 1)) = 2 ^ (ρ + i * K + 1) * 2 ^ (K - 1) from pow_add _ _ _,
      ← Nat.div_div_eq_div_mul, Nat.mod_add_div, Nat.mod_add_div]
  have hF : Function.Injective F := by
    intro a b h
    simp only [F, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h2' : (a.1 : ℕ) / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) =
        (b.1 : ℕ) / 2 ^ (ρ + i * K + 1) % 2 ^ (K - 1) := by
      have := congrArg (fun g => ((Subtype.val g : Fin _) : ℕ)) h2
      simpa using this
    apply Subtype.ext; apply Fin.ext
    rw [key (a.1 : ℕ), key (b.1 : ℕ), h1, h2', h3]
  calc Fintype.card {y : Fin (2 ^ L) // ¬ GuardOK K ρ m y i}
      ≤ 2 ^ (ρ + i * K + 1) * Fintype.card {g : Fin (2 ^ (K - 1)) //
          ¬ (m ≤ (g : ℕ) ∧ (g : ℕ) + m < 2 ^ (K - 1))} * 2 ^ (L - (ρ + i * K + 1 + (K - 1))) := by
        have := Fintype.card_le_of_injective F hF
        simp only [Fintype.card_prod, Fintype.card_fin] at this
        rw [mul_assoc]; exact this
    _ ≤ 2 ^ (ρ + i * K + 1) * (2 * m) * 2 ^ (L - (ρ + i * K + 1 + (K - 1))) := by
        gcongr; exact card_E m (K - 1)
    _ = 2 * m * 2 ^ (L - (K - 1)) := by
        rw [show L - (K - 1) = (ρ + i * K + 1) + (L - (ρ + i * K + 1 + (K - 1))) by omega,
          pow_add]
        ring

/-- Counting triples by a condition on one chunk. -/
theorem card_filter_coord (k : Fin 3) (P : Fin (2 ^ L) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun v : Tri L => P (v k))).card =
      (Finset.univ.filter P).card * (2 ^ L) ^ 2 := by
  have h : Finset.univ.filter (fun v : Tri L => P (v k)) =
      Fintype.piFinset (fun j => if j = k then Finset.univ.filter P else Finset.univ) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hv j
      split_ifs with hj
      · subst hj; simpa using hv
      · simp
    · intro hv
      simpa using hv k
  rw [h, Fintype.card_piFinset, Fin.prod_univ_three]
  fin_cases k <;> simp [Finset.card_univ, Fintype.card_fin] <;> ring

/-- Union bound over the `2n` used guards of `y` and `z`. -/
theorem card_bad_tri (n : ℕ) (hρ : ρ < K) (hL : L = (n + 1) * K) (m : ℕ) :
    (Finset.univ.filter (fun v : Tri L => ¬ Good K ρ n m v)).card * 2 ^ K ≤
      8 * m * n * (2 ^ L) ^ 3 := by
  have hK : 1 ≤ K := by omega
  let A : ℕ → Fin 3 → Finset (Tri L) := fun i k =>
    Finset.univ.filter (fun v : Tri L => ¬ GuardOK K ρ m (v k) i)
  have hsub : Finset.univ.filter (fun v : Tri L => ¬ Good K ρ n m v) ⊆
      (Finset.range n).biUnion (fun i => A i 1 ∪ A i 2) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Good, not_forall] at hv
    obtain ⟨i, hi, h⟩ := hv
    simp only [A, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨i, hi, by tauto⟩
  have hone : ∀ i < n, ∀ k : Fin 3, (A i k).card * 2 ^ K ≤ 4 * m * (2 ^ L) ^ 3 := by
    intro i hi k
    have hpos : ρ + (i + 1) * K ≤ L := by
      have h1 := Nat.mul_le_mul_right K (show i + 1 ≤ n by omega)
      have h2 : (n + 1) * K = n * K + K := by ring
      rw [hL]; omega
    have h1 := card_guard_fail K ρ L hK m i hpos
    rw [Fintype.card_subtype] at h1
    simp only [A]
    rw [card_filter_coord L k (fun y : Fin (2 ^ L) => ¬ GuardOK K ρ m (y : ℕ) i)]
    have h2 : 2 ^ (L - (K - 1)) * 2 ^ K = 2 * 2 ^ L := by
      rw [← pow_add, ← pow_succ']
      congr 1
      have : K ≤ L := by
        have := Nat.mul_le_mul_right K (show 1 ≤ n + 1 by omega)
        rw [hL]; omega
      omega
    calc (Finset.univ.filter (fun y : Fin (2 ^ L) => ¬ GuardOK K ρ m (y : ℕ) i)).card *
          (2 ^ L) ^ 2 * 2 ^ K
        ≤ 2 * m * 2 ^ (L - (K - 1)) * (2 ^ L) ^ 2 * 2 ^ K := by gcongr
      _ = 4 * m * (2 ^ L) ^ 3 := by
        rw [mul_assoc (2 * m * 2 ^ (L - (K - 1))), mul_comm ((2 ^ L) ^ 2), ← mul_assoc,
          mul_assoc (2 * m), h2]
        ring
  calc (Finset.univ.filter (fun v : Tri L => ¬ Good K ρ n m v)).card * 2 ^ K
      ≤ (∑ i ∈ Finset.range n, ((A i 1).card + (A i 2).card)) * 2 ^ K := by
        gcongr
        exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
          (Finset.sum_le_sum (fun i _ => Finset.card_union_le _ _)))
    _ = ∑ i ∈ Finset.range n, ((A i 1).card * 2 ^ K + (A i 2).card * 2 ^ K) := by
        rw [Finset.sum_mul]
        simp only [add_mul]
    _ ≤ ∑ _i ∈ Finset.range n, (4 * m * (2 ^ L) ^ 3 + 4 * m * (2 ^ L) ^ 3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact add_le_add (hone i hi' 1) (hone i hi' 2)
    _ = 8 * m * n * (2 ^ L) ^ 3 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

variable (N₀ N₁ N₂ N₃ : ℕ)

/-- **Exceptional count**, exact integer form: `|B| · 2^K ≤ 8 m (f-1) · M`. -/
theorem card_bad (f m : ℕ) (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) :
    Nat.card {a : Addr N₀ N₁ N₂ N₃ L // Bad N₀ N₁ N₂ N₃ L K ρ f m a} * 2 ^ K ≤
      8 * m * (f - 1) * Nat.card (Addr N₀ N₁ N₂ N₃ L) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  have h : Finset.univ.filter (fun a : Addr N₀ N₁ N₂ N₃ L => Bad N₀ N₁ N₂ N₃ L K ρ f m a) =
      (Finset.univ : Finset (Spec N₀ N₁ N₂ N₃)) ×ˢ
        Finset.univ.filter (fun v : Tri L => ¬ Good K ρ (f - 1) m v) := by
    ext ⟨sp, v⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter]
    simp [Bad]
  have hL' : L = (f - 1 + 1) * K := by rw [hL, Nat.sub_add_cancel hf]
  have hb := card_bad_tri K ρ L (f - 1) hρ hL' m
  have hT : Fintype.card (Tri L) = (2 ^ L) ^ 3 := by simp [Tri]
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_prod (Spec N₀ N₁ N₂ N₃) (Tri L), hT]
  calc Fintype.card (Spec N₀ N₁ N₂ N₃) *
        (Finset.univ.filter (fun v : Tri L => ¬ Good K ρ (f - 1) m v)).card * 2 ^ K
      = Fintype.card (Spec N₀ N₁ N₂ N₃) *
        ((Finset.univ.filter (fun v : Tri L => ¬ Good K ρ (f - 1) m v)).card * 2 ^ K) := by ring
    _ ≤ Fintype.card (Spec N₀ N₁ N₂ N₃) * (8 * m * (f - 1) * (2 ^ L) ^ 3) := by gcongr
    _ = 8 * m * (f - 1) * (Fintype.card (Spec N₀ N₁ N₂ N₃) * (2 ^ L) ^ 3) := by ring

/-- **Exceptional fraction** in the paper's form, `|B| ≤ min{1, 8m(f-1)2^{-K}} M`. -/
theorem card_bad_le (f m : ℕ) (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) :
    (Nat.card {a : Addr N₀ N₁ N₂ N₃ L // Bad N₀ N₁ N₂ N₃ L K ρ f m a} : ℝ) ≤
      min 1 (8 * m * ((f - 1 : ℕ) : ℝ) / 2 ^ K) * Nat.card (Addr N₀ N₁ N₂ N₃ L) := by
  rw [min_mul_of_nonneg _ _ (Nat.cast_nonneg _)]
  apply le_min
  · rw [one_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_subtype_le _
  · have h := card_bad K ρ L N₀ N₁ N₂ N₃ f m hρ hL hf
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact_mod_cast h

/-- The paper's constant: margin `m = 10` (guards `10 ≤ g ≤ 2^{K-1} - 11`) gives `c = 80`. -/
theorem card_bad_le_paper (f : ℕ) (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f) :
    (Nat.card {a : Addr N₀ N₁ N₂ N₃ L // Bad N₀ N₁ N₂ N₃ L K ρ f 10 a} : ℝ) ≤
      min 1 (80 * ((f - 1 : ℕ) : ℝ) / 2 ^ K) * Nat.card (Addr N₀ N₁ N₂ N₃ L) := by
  have h := card_bad_le K ρ L N₀ N₁ N₂ N₃ f 10 hρ hL hf
  norm_num at h ⊢
  exact h

end Density

/-! ### Main theorem -/

/-- **Main theorem.** For `ρ < K`, `L = f K`, `f ≥ 1`, guard margin `m ≥ 1`, every physical
order `σ`, and every key width `k` with `M ≤ 2^k`:
1. the stream program `prog σ` moves the record at rank `enc σ a` to rank `enc σ (S₀ a)`, with
   eight rotations and at most ten swaps;
2. `S₀ = packedS` agrees with `T₀ = idealT` off `Bad`, and both preserve `Bad`;
3. the vendored repair pipeline outputs the stream of `T₀`;
4. the top fixup completes the target: `xorSel = topFix * idealT`;
5. `|Bad| ≤ min 1 (8 m (f - 1) 2^{-K}) · M`. -/
theorem packedXor_main (N₀ N₁ N₂ N₃ L K ρ f m : ℕ) (hρ : ρ < K) (hL : L = f * K) (hf : 1 ≤ f)
    (hm : 1 ≤ m) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (hk : rectSize N₀ N₁ N₂ N₃ L ≤ 2 ^ k)
    (data : Addr N₀ N₁ N₂ N₃ L → List Bool) :
    (∀ a, rankEquiv N₀ N₁ N₂ N₃ L
        (runPhys N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ) (toPhys N₀ N₁ N₂ N₃ L σ a)) =
      enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a)) ∧
    (prog σ).countP Instr.isRot = 8 ∧ (prog σ).countP (fun i => !i.isRot) ≤ 10 ∧
    (∀ a, ¬ Bad N₀ N₁ N₂ N₃ L K ρ f m a →
      liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a = liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) a) ∧
    (∀ a, Bad N₀ N₁ N₂ N₃ L K ρ f m (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) a) ↔
      Bad N₀ N₁ N₂ N₃ L K ρ f m a) ∧
    (∀ a, Bad N₀ N₁ N₂ N₃ L K ρ f m (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a) ↔
      Bad N₀ N₁ N₂ N₃ L K ρ f m a) ∧
    pipeline (enc N₀ N₁ N₂ N₃ L σ) (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f))
        (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f)) (Bad N₀ N₁ N₂ N₃ L K ρ f m) k data =
      stream (enc N₀ N₁ N₂ N₃ L σ) (Bad N₀ N₁ N₂ N₃ L K ρ f m)
        (data ∘ (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f)).symm) ∧
    xorSel L K ρ f = topFix L K ρ f * idealT L K ρ f ∧
    (Nat.card {a : Addr N₀ N₁ N₂ N₃ L // Bad N₀ N₁ N₂ N₃ L K ρ f m a} : ℝ) ≤
      min 1 (8 * m * ((f - 1 : ℕ) : ℝ) / 2 ^ K) * Nat.card (Addr N₀ N₁ N₂ N₃ L) :=
  ⟨prog_rank N₀ N₁ N₂ N₃ L K ρ f σ, (prog_counts σ).1, (prog_counts σ).2,
    packed_agrees N₀ N₁ N₂ N₃ L K ρ f m hρ hL hf hm,
    idealT_preserves_bad N₀ N₁ N₂ N₃ L K ρ f m (by omega),
    packed_preserves_bad N₀ N₁ N₂ N₃ L K ρ f m hρ hL hf hm,
    repair_exact N₀ N₁ N₂ N₃ L K ρ f m hρ hL hf hm σ k hk data,
    xorSel_eq L K ρ f (by omega) hf,
    card_bad_le K ρ L N₀ N₁ N₂ N₃ f m hρ hL hf⟩

end IntegerMultBounds.MathlibTM2.Layer.PackedXor
