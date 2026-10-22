module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueShears
public import IntegerMultBounds.MathlibTM2.Routing.SparseProfiles
public import Mathlib.Data.Finset.Card

/-!
# Sparse bulk passes and a bounded elementary terminal schedule

This closes the logical boundary gap: complete-segment targets are partitioned
by residue, and every remaining target receives a singleton XOR. The number of
singleton calls is at most K. Executing those XORs on tape remains separate.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι]

def elementaryShears (source : ι → ι) : List ι → (ι → Bool) → (ι → Bool)
  | [], x => x
  | i :: is, x => shear {i} source (elementaryShears source is x)

theorem elementaryShears_eq (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (x : ι → Bool) :
    elementaryShears source targets.toList x = shear targets source x := by
  have he (ks : List ι) (hks : ∀ i ∈ ks, i ∈ targets) :
      elementaryShears source ks x = partitionShears targets source id ks x := by
    induction ks with
    | nil => rfl
    | cons i is ih =>
      have hi := hks i (by simp)
      have hf : (targets.filter fun j => id j = i) = {i} := by
        ext j
        simp only [Finset.mem_filter, id_eq, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩
      simp only [elementaryShears, partitionShears, hf]
      rw [ih (fun j hj => hks j (by simp [hj]))]
  rw [he _ (by simp), partitionShears_eq _ _ _ hsource _ targets.nodup_toList]
  congr 1
  ext i
  simp

def bulkTargets (targets : Finset (Fin n)) (K : ℕ) : Finset (Fin n) :=
  targets.filter fun i => i.val + K ≤ n

def terminalTargets (targets : Finset (Fin n)) (K : ℕ) : Finset (Fin n) :=
  targets.filter fun i => ¬ i.val + K ≤ n

theorem terminalTargets_card_le (targets : Finset (Fin n)) (K : ℕ) :
    (terminalTargets targets K).card ≤ K := by
  have h := Finset.card_le_card_of_injOn (s := terminalTargets targets K)
    (t := Finset.range K) (fun i => i.val - (n - K)) ?_ ?_
  · simpa using h
  · intro i hi
    have ht := (Finset.mem_filter.mp hi).2
    have hb := i.isLt
    change i.val - (n - K) ∈ Finset.range K
    rw [Finset.mem_range]
    omega
  · intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    change i.val - (n - K) = j.val - (n - K) at he
    apply Fin.ext
    omega

/-- No coordinate is lost between sparse bulk passes and terminal singleton XORs. -/
theorem bulk_terminal_shears_eq (targets : Finset (Fin n)) (source : Fin n → Fin n)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (K : ℕ) (hK : 0 < K)
    (x : Fin n → Bool) :
    partitionShears (bulkTargets targets K) source
      (fun i => (⟨i.val % K, Nat.mod_lt _ hK⟩ : Fin K)) (List.finRange K)
      (elementaryShears source (terminalTargets targets K).toList x) =
        shear targets source x := by
  have hs (a : Finset (Fin n)) (ha : a ⊆ targets) : ∀ i ∈ a, source i ∉ a :=
    fun i hi hj => hsource i (ha hi) (ha hj)
  have hb : ∀ i ∈ bulkTargets targets K, source i ∉ bulkTargets targets K :=
    hs _ (Finset.filter_subset _ _)
  have ht : ∀ i ∈ terminalTargets targets K, source i ∉ terminalTargets targets K :=
    hs _ (Finset.filter_subset _ _)
  rw [residueShears_eq _ _ hb K hK, elementaryShears_eq _ _ ht]
  have hu : bulkTargets targets K ∪ terminalTargets targets K = targets := by
    ext i
    simp only [bulkTargets, terminalTargets, Finset.mem_union, Finset.mem_filter]
    tauto
  have hd : Disjoint (bulkTargets targets K) (terminalTargets targets K) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  have hs' : ∀ i ∈ bulkTargets targets K ∪ terminalTargets targets K,
      source i ∉ bulkTargets targets K ∪ terminalTargets targets K := by
    simpa only [hu] using hsource
  rw [shear_union _ _ source hd hs', hu]

end IntegerMultBounds.MathlibTM2.Routing
