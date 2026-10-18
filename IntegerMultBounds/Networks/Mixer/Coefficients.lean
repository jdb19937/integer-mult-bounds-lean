module

public import IntegerMultBounds.Networks.GroupedCoefficients
public import IntegerMultBounds.Networks.Mixer.Global

/-! Static coefficient bounds of the grouped mixer network: every row of every
group, in every stage and invocation, uses only `±1`, `0` and coefficients of the
gather, injection and scatter matrices. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Coefficients

open Circuit GroupedCircuit CircuitCoefficients GroupedCoefficients Scalar

variable {R : Type*} [CommRing R] [DecidableEq R] {n a c M : ℕ}
  (P : R → Prop) (hn : ∀ x, P x → P (-x)) (h0 : P 0) (h1 : P 1)
  (kind : Fin a → Kind n M) (G : Fin c → Fin n → R) (J : Fin n → Fin a → R)
  (H : Fin n → Fin c → R)
  (hG : ∀ i j, P (G i j)) (hJ : ∀ i j, P (J i j)) (hH : ∀ i j, P (H i j))

include hn h1 in
theorem unit_coeff {ε : R} (hε : ε = 1 ∨ ε = -1) : P ε := by
  rcases hε with rfl | rfl
  · exact h1
  · exact hn _ h1

theorem mixRow_all {s : ℕ} (ε : R) (hε : P ε) :
    AllGroups P (mixRow (s := s) (c := c) kind ε) := by
  intro g hg row hrow t ht
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨p, -, rfl⟩ := (mem_mixRows kind).mp hrow
  obtain ⟨q, -, rfl⟩ := (mem_mixTerms kind).mp ht
  exact hε

include h0 in
theorem copyRow_all {s : ℕ} (ε : R) (hε : P ε) :
    AllGroups P (copyRow (s := s) (c := c) kind ε) := by
  intro g hg row hrow t ht
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, rfl⟩ := mem_fanout_rows hrow
  have he := List.mem_singleton.mp ht
  subst t
  change P (ε * Scalar.copyMatrix kind i j)
  unfold Scalar.copyMatrix
  split_ifs
  · rwa [mul_one]
  · rwa [mul_zero]

include hn h0 h1 hG hJ hH in
theorem forward_all {s : ℕ} : AllGroups P (Scalar.forward (s := s) kind G J H) := by
  have hm := unit_coeff P hn h1 (Or.inr rfl)
  unfold Scalar.forward
  repeat' apply GroupedCoefficients.append
  all_goals first
    | exact mixRow_all P kind _ h1
    | exact mixRow_all P kind _ hm
    | exact copyRow_all P h0 kind _ h1
    | exact copyRow_all P h0 kind _ hm
    | exact GroupedCoefficients.fanin P _ _ _ _ (fun i j => hJ i j)
    | exact GroupedCoefficients.fanin P _ _ _ _ (fun i j => hn _ (hJ i j))
    | exact GroupedCoefficients.singleton P _ (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hH i j))
    | exact GroupedCoefficients.singleton P _
        (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hn _ (hH i j)))
    | exact GroupedCoefficients.singleton P _ (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hG i j))
    | exact GroupedCoefficients.singleton P _
        (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hn _ (hG i j)))

include hn h0 h1 hG hJ hH in
theorem inverse_all {s : ℕ} : AllGroups P (Scalar.inverse (s := s) kind G J H) := by
  have hm := unit_coeff P hn h1 (Or.inr rfl)
  unfold Scalar.inverse
  repeat' apply GroupedCoefficients.append
  all_goals first
    | exact mixRow_all P kind _ h1
    | exact mixRow_all P kind _ hm
    | exact copyRow_all P h0 kind _ h1
    | exact copyRow_all P h0 kind _ hm
    | exact GroupedCoefficients.fanin P _ _ _ _ (fun i j => hJ i j)
    | exact GroupedCoefficients.fanin P _ _ _ _ (fun i j => hn _ (hJ i j))
    | exact GroupedCoefficients.singleton P _ (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hH i j))
    | exact GroupedCoefficients.singleton P _
        (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hn _ (hH i j)))
    | exact GroupedCoefficients.singleton P _ (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hG i j))
    | exact GroupedCoefficients.singleton P _
        (GroupedCoefficients.matrix P _ _ _ _ (fun i j => hn _ (hG i j)))

variable {B A C : Type*}
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)

include hn h0 h1 hG hJ hH in
/-- Every coefficient of the global mixer network satisfies `P`. -/
theorem program_all : AllGroups P (Global.program eB eA eC kind G J H) := by
  have hloc : ∀ j, AllGroups P (Global.localGroups kind G J H j) := by
    intro j
    unfold Global.localGroups
    split
    · exact GroupedCoefficients.rename P _ _ (inverse_all P hn h0 h1 kind G J H hG hJ hH)
    · exact forward_all P hn h0 h1 kind G J H hG hJ hH
  have hstage : ∀ j, AllGroups P (Global.stage eB eA eC kind G J H j) := by
    intro j g hg
    obtain ⟨q, -, hq⟩ := List.mem_flatMap.mp hg
    exact GroupedCoefficients.embed P _ _ (hloc j) g hq
  unfold Global.program
  exact GroupedCoefficients.append P _ _ (GroupedCoefficients.append P _ _ (hstage 0) (hstage 1))
    (hstage 2)

end IntegerMultBounds.Networks.Mixer.Coefficients
