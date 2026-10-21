module

public import IntegerMultBounds.MathlibTM2.M8.RevNetwork
public import IntegerMultBounds.MathlibTM2.M8.Rev.Heights
public import IntegerMultBounds.MathlibTM2.M8.Machine.Coordinates

/-!
# The stage-2 PR97 node at the machine prime

`rev97` uses a prime chosen beyond its denominators. Here the heights are explicit, so the
machine prime `Shared50ModularControl.prime`, beyond `Networks.coefficientBound`, serves:

* the generic basis has natural entries at most `2 ^ 55` (`basis97_le`): its degree bound is
  `529 + 529 · 530 · s` with `s` the stage-1 rank sum (`degree97_le`);
* its inverse has heights at most `2 ^ 68770` (`bounded_basis97'`), and every conjugated frame
  change `G U G⁻¹` heights at most `2 ^ conjE` (`bounded_conj`);
* so every number of every stage-2 edge program, every denominator of `G⁻¹` and the frame bound
  lie below the machine prime (`nums97_lt`), and every coefficient is within
  `coefficientBound` (`coeff_bound97`).

`rev97m` is the stage-2 node at the machine prime, and `runs_rev97m` its machine certificate
(`RevRuns`): the machine prime, coefficients within the bound, and `width ≤ roleCount`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global
open IntegerMultBounds.Swap.Modular (Admissible denominators)
open ReversedExchange (rev)
open Height (Bounded)
open Shared50ModularControl (prime)

/-- The machine requirements of a reversed network. -/
structure RevRuns (N : RevNetwork) : Prop where
  prime_eq : N.prime = Shared50ModularControl.prime
  coeff_bound : ∀ i p, Step.edge i p ∈ N.control → ∀ op ∈ p, Machine.Coordinates.CoeffBounded op
  width_le_roleCount : N.width ≤ N.roleCount

namespace Rev

theorem edgeMats_rank_sum {ι : Type} [DecidableEq ι] {d : ℕ} :
    ∀ L : List (FStep ι d), ((edgeMats L).map Matrix.rank).sum = edgeRanks L
  | [] => rfl
  | s :: rest => by
    have ih := edgeMats_rank_sum rest
    cases s <;> simp [edgeMats, edgeRanks, ih]

end Rev

/-! ### The basis -/

open Classical

theorem card_sizes_le (r : ℕ) : (GenericBasis.sizes (m := 529) r).card ≤ r := by
  calc (GenericBasis.sizes (m := 529) r).card ≤ (Finset.Icc 1 r).card :=
        Finset.card_le_card_of_injOn (fun i => i.val)
          (fun i hi => by
            simp only [GenericBasis.sizes, Finset.coe_filter, Finset.mem_univ, true_and] at hi
            simpa using hi)
          (fun i _ j _ h => Fin.ext h)
    _ = r := by simp

theorem rank_sum97 : ∑ j : Fin edges97.length, (edges97.get j).rank ≤ 57403754177 := by
  have h := Fin.sum_univ_fun_getElem edges97 Matrix.rank
  simp only [List.get_eq_getElem]
  rw [h, edges97_def, Rev.edgeMats_rank_sum, ← calls_physOf]
  exact calls_node_le

theorem sizes_sum_le (r : ℕ) :
    ∑ i ∈ GenericBasis.sizes (m := 529) r, i.val * (529 + 1) ≤ r * (529 * 530) := by
  calc ∑ i ∈ GenericBasis.sizes (m := 529) r, i.val * (529 + 1)
      ≤ ∑ _i ∈ GenericBasis.sizes (m := 529) r, 529 * 530 :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
    _ = (GenericBasis.sizes (m := 529) r).card * (529 * 530) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ r * (529 * 530) := Nat.mul_le_mul_right _ (card_sizes_le r)

theorem degree_le_of {J : ℕ} (r : Fin J → ℕ) {s : ℕ} (hs : ∑ j, r j ≤ s) :
    GenericBasis.degreeBound 529 r ≤ 529 + s * (529 * 530) := by
  unfold GenericBasis.degreeBound
  calc 529 + ∑ j, ∑ i ∈ GenericBasis.sizes (m := 529) (r j), i.val * (529 + 1)
      ≤ 529 + ∑ j, r j * (529 * 530) := Nat.add_le_add_left (Finset.sum_le_sum fun j _ => sizes_sum_le _) _
    _ = 529 + (∑ j, r j) * (529 * 530) := by rw [Finset.sum_mul]
    _ ≤ 529 + s * (529 * 530) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _

theorem degree97_le :
    GenericBasis.degreeBound 529 (fun j : Fin edges97.length => (edges97.get j).rank) ≤ 2 ^ 55 :=
  (degree_le_of _ rank_sum97).trans (by norm_num)

theorem basis97_le (a b : Fin 529) : (Classical.choose exists_basis97) a b ≤ 2 ^ 55 :=
  ((Classical.choose_spec exists_basis97).1 a b).trans degree97_le

theorem bounded_basis97 : Bounded basis97 (2 ^ 55) := by
  rw [basis97_def]; exact Rev.bounded_natCast basis97_le

/-- The height exponent of the inverse basis. -/
irreducible_def invE : ℕ := 2 * (529 * (10 + 55))

theorem invE_le : invE ≤ 2 ^ 53000 := by
  rw [invE_def]
  exact (show 2 * (529 * (10 + 55)) ≤ 2 ^ 17 by norm_num).trans (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem bounded_basis97' : Bounded basis97' (2 ^ invE) := by
  rw [basis97'_def, basis97_def, invE_def]
  exact Rev.bounded_inv_natCast basis97_le (k := 10) (by norm_num)

/-! ### The conjugated frame changes -/

/-- The height exponent of a conjugated frame change. -/
irreducible_def conjE : ℕ := 529 * (529 * (55 + 33220 + 1) + invE + 1)

theorem ten_pow_le : (10 : ℕ) ^ 10000 ≤ 2 ^ 33220 := by decide +kernel

theorem bounded_edge {U : Mat 529} (hU : U ∈ edges97) : Bounded U (2 ^ 33220) := fun i j => by
  have h := (edgeMat_edges97 U hU).bound i j
  exact (max_le h.1 h.2).trans ten_pow_le

theorem conjE_eq : Fintype.card (Fin 529) * (Fintype.card (Fin 529) * (55 + 33220 + 1) + invE + 1) =
    conjE := by
  rw [Fintype.card_fin, conjE_def]

theorem conjE_le : conjE + 1 ≤ 2 ^ 36 := by
  rw [conjE_def, invE_def]; norm_num

theorem bounded_conj {U : Mat 529} (hU : U ∈ edges97) :
    Bounded (basis97 * U * basis97') (2 ^ conjE) :=
  (Height.bounded_mul (Height.bounded_mul bounded_basis97 (bounded_edge hU)) bounded_basis97').pow_mono
    conjE_eq.le

theorem expOf_conj {U : Mat 529} (hU : U ∈ edges97) :
    Exchange.expOf (basis97 * U * basis97' * rev 529) ≤ 2 ^ 36 :=
  (Rev.expOf_le (Rev.bounded_mul_rev (bounded_conj hU))).trans conjE_le

/-! ### The machine prime -/

/-- Every number a prime must avoid is below any prime beyond `coefficientBound`, when the
conjugated frame changes and the inverse basis are bounded. -/
theorem nums_lt_of {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 529) {edges : List (Mat m)} {G G' : Mat m}
    (hE : ∀ U ∈ edges, Exchange.expOf (G * U * G' * rev m) ≤ 2 ^ 36) {a : ℕ}
    (hG' : Bounded G' (2 ^ a)) (ha : a ≤ 2 ^ 53000) {q : ℕ} (hq : coefficientBound < q) :
    ∀ e ∈ nums edges G G', e < q := by
  intro e he
  unfold nums at he
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_biUnion] at he
  rcases he with (⟨j, -, hj⟩ | hj) | hj
  · exact lt_of_le_of_lt (Rev.revNumbers_le_coefficientBound _ (by simpa using hm1) (by simpa using hm)
      (hE _ (List.get_mem _ _)) e hj) hq
  · exact lt_of_le_of_lt ((Exchange.den_mem_le hG' le_rfl hj).trans
      (Exchange.le_coefficientBound ha)) hq
  · rw [Finset.mem_singleton] at hj
    subst hj
    rw [edgeBound_def]
    refine lt_of_le_of_lt (ten_pow_le.trans
      (Exchange.le_coefficientBound ((show 33220 ≤ 2 ^ 16 by norm_num).trans
        (pow_le_pow_right₀ (by norm_num) (by norm_num))))) hq

theorem nums97_lt : ∀ e ∈ nums edges97 basis97 basis97', e < prime :=
  nums_lt_of (by norm_num) le_rfl (fun _ hU => expOf_conj hU) bounded_basis97' invE_le
    Shared50ModularControl.coefficientBound_lt_prime

theorem rev_admissible_machine (b : ℕ) : Admissible (prime ^ b) (rev 529 : Mat 529) := fun i j => by
  have : ((rev 529 : Mat 529) i j).den = 1 := by
    simp only [rev, Matrix.of_apply]
    split_ifs <;> rfl
  rw [this]
  exact Nat.coprime_one_left _

theorem coeff_bound97 {i : Wire} {p : FieldProgram 529} (h : Step.edge i p ∈ control97) :
    ∀ op ∈ p, Machine.Coordinates.CoeffBounded op := by
  obtain ⟨U, hU, rfl, -⟩ := edge_interchanges h
  intro op hop r hr
  exact Rev.revProgram_coeffs_le_coefficientBound _ (by simp) (by simp) (expOf_conj hU) op hop r hr

/-- **The stage-2 PR97 node at the machine prime.** -/
def rev97m : RevNetwork where
  World := World
  Temp := Temp
  roleCount := 108516254
  roleEquiv := (Fintype.equivFinOfCardEq card_world).symm
  tempCount := 3217908
  tempEquiv := (Fintype.equivFinOfCardEq card_temp).symm
  width := 529
  two_le_width := by norm_num
  prime := prime
  prime_prime := Shared50ModularControl.prime_prime
  prime_odd := fun h => by have := Shared50ModularControl.prime_odd; omega
  control := control97
  route := route
  route_involutive := route_involutive
  rankSum := calls (physOf framedNode)
  calls_exact := calls_rev97
  legal_mod := fun b i p h => by
    obtain ⟨U, hU, rfl, -⟩ := edge_interchanges h
    exact Rev.revProgram_specialize_legal Shared50ModularControl.prime_prime
      (edge_nums nums97_lt hU) b
  xor_gate := fun g hg =>
    valid_gates framedNode gInit tempZero valid_node g (Rev.mem_revPhysOf_gate _ _ _ g hg)
  block := fun i p h j k => by
    obtain ⟨U, hU, rfl, -⟩ := edge_interchanges h
    rw [Rev.revProgram_interchanges]
    exact Rev.mem_revProgram_interchange _ (generic97 hU) j k
  run_identity := fun b f stored hz i a => by
    rw [run_inst _ (fun x y : Wire => Classical.propDecidable (x = y))]
    exact Rev.rev_node_run (TwistedExchange.atomRev_atomRev f)
      (fun c => funext fun x => by simp)
      (basis_of_nums Shared50ModularControl.prime_prime nums97_lt basis97_den basis97_inv
        basis97_inv' b) (rev_admissible_machine b)
      (fun U hU => edge_nums nums97_lt (by rw [edges97_def]; exact hU)) stored hz i a

/-- **The machine certificate** of the stage-2 node. -/
theorem runs_rev97m : RevRuns rev97m where
  prime_eq := rfl
  coeff_bound := fun _ _ h => coeff_bound97 h
  width_le_roleCount := by change 529 ≤ 108516254; norm_num

end

end IntegerMultBounds.MathlibTM2.M8
