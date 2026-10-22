module

public import IntegerMultBounds.MathlibTM2.M8.Global.Node

/-! The global swap follows from any two local shears on the existing roles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- A local shear adds each source to its target and preserves the other registers. -/
def LocalShear (p : Circuit.Program LW (ZMod 2)) : Prop :=
  ∀ d : LW → ZMod 2, (∀ c, d (.inr c) = 0) →
    (∀ t, t < leafCount → Circuit.run p d (.inl (.y t)) = d (.inl (.y t)) + d (.inl (.x t))) ∧
    (∀ r : Reg, r.isY = false → Circuit.run p d (.inl r) = d (.inl r))

/-- The two placed local shears followed by the data-pair correction. -/
def nodeProgram (p q : Circuit.Program LW (ZMod 2)) : Circuit.Program Wire (ZMod 2) :=
  (allV.flatMap fun T => p.map (gateMap (place1 T))) ++
  (allV.flatMap fun S => q.map (gateMap (place2 S))) ++
  (allPairs.flatMap fun r => (corrGates r.1 r.2).map FGate.gate)

section
variable (p q : Circuit.Program LW (ZMod 2))
  (hp : OnWires InR p) (hq : OnWires InR q) (hprun : LocalShear p) (hqrun : LocalShear q)

include hp in
theorem placed1_on (T : V) : OnWires (W1 T) (p.map (gateMap (place1 T))) := by
  intro g hg k hk
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [touched_gateMap, List.mem_map] at hk
  obtain ⟨w, hw, rfl⟩ := hk
  exact ⟨w, hp g' hg' w hw, rfl⟩

include hq in
theorem placed2_on (S : V) : OnWires (W2 S) (q.map (gateMap (place2 S))) := by
  intro g hg k hk
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [touched_gateMap, List.mem_map] at hk
  obtain ⟨w, hw, rfl⟩ := hk
  exact ⟨w, hq g' hg' w hw, rfl⟩

include hp hprun in
/-- Invocation `T` of stage one adds `X ⋅ T` into `Y ⋅ T` and restores its side slots. -/
theorem placed1_run (T : V) (c : Wire → ZMod 2) (hz : ∀ c', c (wCentre false T c') = 0) :
    (∀ S, Circuit.run (p.map (gateMap (place1 T))) c (wY S T) =
      c (wY S T) + c (wX S T)) ∧
    (∀ S, Circuit.run (p.map (gateMap (place1 T))) c (wX S T) = c (wX S T)) ∧
    (∀ s, Circuit.run (p.map (gateMap (place1 T))) c (wSide false T s) =
      c (wSide false T s)) := by
  obtain ⟨h1, -⟩ := run_map_on (place1_injOn T) _ hp c
  have hrun := hprun (c ∘ place1 T) fun c' => hz c'
  refine ⟨fun S => ?_, fun S => ?_, fun s => ?_⟩
  · rw [← place1_y, h1 _ (show InR (.inl (.y S)) from S.2), hrun.1 S S.2]
    simp only [Function.comp, place1_x, place1_y]
  · rw [← place1_x, h1 _ (show InR (.inl (.x S)) from S.2), hrun.2 _ rfl]
    simp only [Function.comp, place1_x]
  · rw [← place1_aux, h1 _ (show InR (.inl (.aux s)) from s.2), hrun.2 _ rfl]
    simp only [Function.comp, place1_aux]

include hq hqrun in
/-- Invocation `S` of stage two adds `Y S ⋅` into `X S ⋅` and restores its side slots. -/
theorem placed2_run (S : V) (c : Wire → ZMod 2) (hz : ∀ c', c (wCentre true S c') = 0) :
    (∀ T, Circuit.run (q.map (gateMap (place2 S))) c (wX S T) =
      c (wX S T) + c (wY S T)) ∧
    (∀ T, Circuit.run (q.map (gateMap (place2 S))) c (wY S T) = c (wY S T)) ∧
    (∀ s, Circuit.run (q.map (gateMap (place2 S))) c (wSide true S s) =
      c (wSide true S s)) := by
  obtain ⟨h1, -⟩ := run_map_on (place2_injOn S) _ hq c
  have hrun := hqrun (c ∘ place2 S) fun c' => hz c'
  refine ⟨fun T => ?_, fun T => ?_, fun s => ?_⟩
  · rw [← place2_y, h1 _ (show InR (.inl (.y T)) from T.2), hrun.1 T T.2]
    simp only [Function.comp, place2_x, place2_y]
  · rw [← place2_x, h1 _ (show InR (.inl (.x T)) from T.2), hrun.2 _ rfl]
    simp only [Function.comp, place2_x]
  · rw [← place2_aux, h1 _ (show InR (.inl (.aux s)) from s.2), hrun.2 _ rfl]
    simp only [Function.comp, place2_aux]

include hp hq hprun hqrun in
theorem nodeProgram_scalar (c : Wire → ZMod 2) (hz : ∀ t : Temp, c (.inr t) = 0) :
    (∀ S T, Circuit.run (nodeProgram p q) c (wX S T) = c (wY S T)) ∧
    (∀ S T, Circuit.run (nodeProgram p q) c (wY S T) = c (wX S T)) ∧
    (∀ b k s, Circuit.run (nodeProgram p q) c (wSide b k s) = c (wSide b k s)) := by
  rw [nodeProgram, Circuit.run_append, Circuit.run_append]
  obtain ⟨d1, d1'⟩ := run_flatMap_disjoint _ W1 (placed1_on p hp) W1_disj allV allV_nodup c
  generalize Circuit.run (allV.flatMap fun T => p.map (gateMap (place1 T))) c = e1
    at d1 d1' ⊢
  obtain ⟨d2, d2'⟩ := run_flatMap_disjoint _ W2 (placed2_on q hq) W2_disj allV allV_nodup e1
  generalize Circuit.run (allV.flatMap fun S => q.map (gateMap (place2 S))) e1 = e2
    at d2 d2' ⊢
  obtain ⟨d3, d3'⟩ := run_flatMap_disjoint (fun p => (corrGates p.1 p.2).map FGate.gate) Wc corr_on
    Wc_disj allPairs allPairs_nodup e2
  have hW1X (S T : V) : W1 T (wX S T) := ⟨.inl (.x S), S.2, place1_x T S⟩
  have hW1Y (S T : V) : W1 T (wY S T) := ⟨.inl (.y S), S.2, place1_y T S⟩
  have hW1s (T : V) (s : Slot) : W1 T (wSide false T s) := ⟨.inl (.aux s), s.2, place1_aux T s⟩
  have hW2X (S T : V) : W2 S (wX S T) := ⟨.inl (.y T), T.2, place2_y S T⟩
  have hW2Y (S T : V) : W2 S (wY S T) := ⟨.inl (.x T), T.2, place2_x S T⟩
  have hW2s (S : V) (s : Slot) : W2 S (wSide true S s) := ⟨.inl (.aux s), s.2, place2_aux S s⟩
  have hnot1 : ∀ k, (∀ T w, InR w → place1 T w ≠ k) → ∀ T ∈ allV, ¬ W1 T k :=
    fun k h T _ ⟨w, hw, he⟩ => h T w hw he
  have hnot2 : ∀ k, (∀ S w, InR w → place2 S w ≠ k) → ∀ S ∈ allV, ¬ W2 S k :=
    fun k h S _ ⟨w, hw, he⟩ => h S w hw he
  have hcentre1 : ∀ T c', e1 (wCentre true T c') = 0 := by
    intro T c'
    rw [d1' _ (hnot1 _ fun T' w hw he => by
      rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he)]
    exact hz _
  have hcorr2 : ∀ S T, e2 (wCorr S T) = 0 := by
    intro S T
    rw [d2' _ (hnot2 _ fun S' w hw he => by
      rcases place2_cases S' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre, wCorr] at he),
      d1' _ (hnot1 _ fun T' w hw he => by
      rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre, wCorr] at he)]
    exact hz _
  -- stage one
  have e1X : ∀ S T, e1 (wX S T) = c (wX S T) := fun S T => by
    rw [d1 T (mem_allV T) _ (hW1X S T)]
    exact (placed1_run p hp hprun T c fun c' => hz _).2.1 S
  have e1Y : ∀ S T, e1 (wY S T) = c (wY S T) + c (wX S T) := fun S T => by
    rw [d1 T (mem_allV T) _ (hW1Y S T)]
    exact (placed1_run p hp hprun T c fun c' => hz _).1 S
  -- stage two
  have e2X : ∀ S T, e2 (wX S T) = c (wY S T) := fun S T => by
    rw [d2 S (mem_allV S) _ (hW2X S T), (placed2_run q hq hqrun S e1 (hcentre1 S)).1 T, e1X, e1Y,
      zmod2_cancel]
  have e2Y : ∀ S T, e2 (wY S T) = c (wY S T) + c (wX S T) := fun S T => by
    rw [d2 S (mem_allV S) _ (hW2Y S T), (placed2_run q hq hqrun S e1 (hcentre1 S)).2.1 T, e1Y]
  refine ⟨fun S T => ?_, fun S T => ?_, fun b k s => ?_⟩
  · rw [d3 (S, T) (mem_allPairs S T) _ (Or.inl rfl)]
    exact (corr_x S T e2).trans (e2X S T)
  · rw [d3 (S, T) (mem_allPairs S T) _ (Or.inr (Or.inl rfl))]
    refine (corr_y S T e2).trans ?_
    rw [e2Y, hcorr2, e2X]
    exact zmod2_cancel' _ _
  · rw [d3' _ fun p _ h => by rcases h with h | h | h <;> simp [wX, wY, wSide, wCorr] at h]
    cases b with
    | false =>
      rw [d2' _ (hnot2 _ fun S' w hw he => by
        rcases place2_cases S' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
          rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he),
        d1 k (mem_allV k) _ (hW1s k s)]
      exact (placed1_run p hp hprun k c fun c' => hz _).2.2 s
    | true =>
      rw [d2 k (mem_allV k) _ (hW2s k s), (placed2_run q hq hqrun k e1 (hcentre1 k)).2.2 s,
        d1' _ (hnot1 _ fun T' w hw he => by
        rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
          rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he)]

end

end
end IntegerMultBounds.MathlibTM2.M8.Global
