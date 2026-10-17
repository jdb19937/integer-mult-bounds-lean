module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRoundR
import IntegerMultBounds.MathlibTM2.Layer.TopRFit
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The width hypotheses of the rounded synthetic rounds

`compactSynFitsR_of`: `CompactSynFitsR` holds for every chunk round once `p + 2 ≤ W` and the
chunk addresses fit (`o + K D ≤ Σ es`). The pieces of a round have level at most `D`, at most
`D + 1` of them, and leaf sizes at most `D + m` (the back piece has `backChunks ≤ D` leaves, the
digit pieces fewer than `m`), so every child scale is at most `S = D + m + G`; `topR_fits` then
gives the fit of the array before the shifts from the guard `guardG` and the working width.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity

/-! ### The pieces -/

lemma scaleR_le_add (u : ℕ) (ds : ComplexFramedExecution.Directions) (i : ℕ) :
    scaleR u ds i ≤ u + gateCount (program ds) := by
  cases i with
  | zero => simp [scaleR]
  | succ i => simp [scaleR, nodeExp, progExp_eq]

lemma topPiecesR_mem {ρ K n R₂ : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.OkR K n R₂), ∀ P ∈ topPiecesR hρ pcs h,
      ∃ pc ∈ pcs, P.j = pc.j ∧ P.u = pc.u
  | [], _, P, hP => by simp [topPiecesR] at hP
  | pc :: pcs, h, P, hP => by
    rw [topPiecesR, List.mem_cons] at hP
    rcases hP with rfl | hP
    · exact ⟨pc, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨q, hq, h1, h2⟩ := topPiecesR_mem hρ pcs _ P hP
      exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

lemma topPiecesR_length {ρ K n R₂ : ℕ} (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (h : ∀ pc ∈ pcs, pc.OkR K n R₂), (topPiecesR hρ pcs h).length = pcs.length
  | [], _ => rfl
  | pc :: pcs, h => by rw [topPiecesR, List.length_cons, List.length_cons, topPiecesR_length]

lemma synPcs_facts (K X D' oS J : ℕ) : ∀ t,
    (synPcs K X D' oS J t).length ≤ t ∧ ∀ pc ∈ synPcs K X D' oS J t, pc.j < t ∧ pc.u < m
  | 0 => by simp [synPcs]
  | t + 1 => by
    obtain ⟨h1, h2⟩ := synPcs_facts K X D' oS J t
    rw [synPcs_succ]
    refine ⟨?_, fun pc hpc => ?_⟩
    · by_cases h0 : synDg D' t = 0 <;> simp [h0] <;> omega
    · rcases List.mem_append.1 hpc with hpc | hpc
      · by_cases h0 : synDg D' t = 0
        · simp [h0] at hpc
        · simp only [h0, ite_false, List.mem_singleton] at hpc
          subst hpc
          exact ⟨by simp [synPc], by simp only [synPc, synDg]; exact Nat.mod_lt _ (by norm_num [m])⟩
      · exact ⟨by have := (h2 pc hpc).1; omega, (h2 pc hpc).2⟩

lemma reservedPcs_facts (K oS J B A D : ℕ) (hB : B ≤ D) (hA : A ≤ D) :
    (compactReservedPcs K 0 oS B (oS + K * B) J A).length ≤ D + 1 ∧
      ∀ pc ∈ compactReservedPcs K 0 oS B (oS + K * B) J A, pc.j ≤ D ∧ pc.u ≤ D + m := by
  obtain ⟨h1, h2⟩ := synPcs_facts K 0 A (oS + K * B) J A
  unfold compactReservedPcs
  refine ⟨?_, fun pc hpc => ?_⟩
  · rw [List.length_append]
    split_ifs
    · rw [List.length_nil]; omega
    · rw [List.length_singleton]; omega
  · rcases List.mem_append.1 hpc with hb | hs
    · split_ifs at hb with h0
      · exact absurd hb List.not_mem_nil
      · rw [List.mem_singleton] at hb
        subst hb
        exact ⟨Nat.zero_le _, by show B ≤ D + m; omega⟩
    · have := h2 pc hs
      exact ⟨by omega, by omega⟩

lemma backChunks_le {d g K D : ℕ} (hcap : CompactReservationFits d g K D) : backChunks d g K ≤ D := by
  have he := compactReservation_axes hcap
  generalize CompactGlobalRowPadding.rowAxes NW m d + frontChunks d g K +
    compactReservationActive d g K D = X at he
  omega

lemma compactReservationActive_le (d g K D : ℕ) : compactReservationActive d g K D ≤ D :=
  (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

lemma compactRebasePc_j (R : ℕ) (pc : TopPc) : (compactRebasePc R pc).j = pc.j := by
  cases pc; rfl

lemma compactRebasePc_u (R : ℕ) (pc : TopPc) : (compactRebasePc R pc).u = pc.u := by
  cases pc; rfl

lemma compactTopPcs_facts {d g K D o R₂ : ℕ} (hcap : CompactReservationFits d g K D) :
    (compactTopPcs d g K D o R₂).length ≤ D + 1 ∧
      ∀ pc ∈ compactTopPcs d g K D o R₂, pc.j ≤ D ∧ pc.u ≤ D + m := by
  obtain ⟨h1, h2⟩ := reservedPcs_facts K o (CompactGlobalRowPadding.depth m d) _ _ D
    (backChunks_le hcap) (compactReservationActive_le d g K D)
  unfold compactTopPcs
  refine ⟨by rw [List.length_map]; exact h1, fun pc hpc => ?_⟩
  obtain ⟨pc', hpc', hpc'e⟩ := List.mem_map.1 hpc
  rw [← hpc'e, compactRebasePc_j, compactRebasePc_u]
  exact h2 pc' hpc'

/-! ### The width hypotheses -/

/-- **The width hypotheses of the rounded rounds.** -/
theorem compactSynFitsR_of (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) (hW : p + 2 ≤ W)
    (haddr : ∀ h, synChunk ℓ K h → K * ((h - layB ℓ K) / K * es.length) + K * es.length ≤ es.sum) :
    CompactSynFitsR ds M K es ℓ W l p := by
  intro h hc d g D o ρ n a hKpos hcap hD ha q aT R₂ E gb s working pcs hρ hfitT hpcs hpcsR Ps low hR₂
  have hpf := compactTopPcs_facts (o := o) (R₂ := R₂) hcap
  have hn : n ≤ es.sum :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _).trans (haddr h hc)
  have hna : n + a = es.sum := by simp only [a]; omega
  have hG : ∀ u i, scaleR u ds i ≤ u + gateCount (program ds) := fun u i => scaleR_le_add u ds i
  have hwv : working = W + s + D + guardKc (cGain ds) es.sum l D + gateCount (program ds) + m + 4 :=
    rfl
  refine ⟨fun pc hpc i _ => ?_, fun Y hY z => ?_⟩
  · have h1 := hG pc.u i
    have h2 := (hpf.2 pc hpc).2
    omega
  -- the array before the shifts
  have hR₂' : R₂ ≤ 2 * (1 * 2 ^ a) :=
    (compactTopRows_bounds (d := d) (by omega : 0 < K) (by omega : 0 < 1) ha).2.2.1
  have hPs : Ps = topPieces hρ pcs hpcs := topPiecesR_eq hρ pcs hpcs
  have hinj : ∀ P ∈ Ps, Function.Injective P.e := by
    rw [hPs]; exact compactTopPieces_injective ds hρ pcs hpcs
  have hcover : (Ps.flatMap Piece.bitsList).Perm low := by rw [hPs]
  have hsel : (low.map (Fin.castAdd a) ++ topTop aT ρ K q (n + a) hfitT).Nodup :=
    compactSelection_nodup (by omega) (compactTopSelection_vals ds hcap hρ hpcs hfitT)
  have hs : s = (low.length + (topTop aT ρ K q (n + a) hfitT).length + 1) / 2 +
      (topTop aT ρ K q (n + a) hfitT).length + (Ps.map (Piece.expR ds)).sum + gb := by
    have h1 := compactTop_shiftR ds hcap hρ hpcs hfitT
    have h2 : (topTop aT ρ K q (n + a) hfitT).length = q := by simp [topTop]
    have h3 : s = (D + 1) / 2 + q + (gb + E) := rfl
    rw [h2, h3]
    have h4 : (D + 1) / 2 + q + E = (low.length + q + 1) / 2 + q + (Ps.map (Piece.expR ds)).sum := h1
    omega
  have hj : ∀ P ∈ Ps, P.j ≤ D := by
    intro P hP
    obtain ⟨pc, hpc, hj, -⟩ := topPiecesR_mem hρ pcs hpcsR P hP
    rw [hj]; exact (hpf.2 pc hpc).1
  have hlen : Ps.length ≤ D + 1 := by
    rw [topPiecesR_length]; exact hpf.1
  have hS : ∀ P ∈ Ps, ∀ i < P.j, scaleR P.u ds i ≤ D + m + gateCount (program ds) := by
    intro P hP i _
    obtain ⟨pc, hpc, -, hu⟩ := topPiecesR_mem hρ pcs hpcsR P hP
    have h1 := hG P.u i
    have h2 := (hpf.2 pc hpc).2
    omega
  have hg : (n + a + l + 2) + D * (cGain ds + 1) + D + 6 ≤ gb := by
    show _ ≤ guardG (cGain ds) es.sum l D
    unfold guardG guardKc; rw [hna]; ring_nf; omega
  have hw : (D + m + gateCount (program ds)) + cGain ds * D + s + p + (n + a + l + 2) + 5 ≤
      working := by
    rw [hwv, hna]; unfold guardKc; ring_nf; omega
  exact topR_fits_pre ds hd a l low (topTop aT ρ K q (n + a) hfitT) hR₂ hR₂' Ps hinj hcover hsel gb s
    working p D (D + m + gateCount (program ds)) hs (synZ (n + a) Y) (fun z => hY _ _) hj hlen hS
    hg hw z

end IntegerMultBounds.MathlibTM2.Fast.Main
