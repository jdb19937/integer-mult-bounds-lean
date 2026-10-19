module

public import IntegerMultBounds.MathlibTM2.M8.Global.Auto
public import IntegerMultBounds.MathlibTM2.M8.Local.Word

/-!
# Placing local gate lists on node wires

A local gate list whose wires lie in a set `A` is placed on node wires by a map `e`, injective
on `A`, and a map of frames (`placeG`). On the image of `A` the placed program runs as the local
program (`run_map_on`) and leaves every other wire alone; each placed wire passes through the
placed frames of its local wire (`fseq_place`), and the other wires through none
(`fseq_place_out`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {d d' : ℕ}

/-- Every gate touches only wires of `A`. -/
def OnWires (A : ι → Prop) (p : Circuit.Program ι (ZMod 2)) : Prop :=
  ∀ g ∈ p, ∀ w ∈ FramedCircuit.touched g, A w

/-- `e` is injective on `A`. -/
def InjOn' (e : ι → κ) (A : ι → Prop) : Prop := ∀ a b, A a → A b → e a = e b → a = b

omit [DecidableEq ι] [DecidableEq κ] in
theorem touched_gateMap (e : ι → κ) (g : Circuit.Gate ι (ZMod 2)) :
    FramedCircuit.touched (gateMap e g) = (FramedCircuit.touched g).map e := by
  simp [FramedCircuit.touched, gateMap, List.map_map, Function.comp]

/-- A program on wires of `A` reads only them. -/
theorem run_congr_on {A : ι → Prop} : ∀ (p : Circuit.Program ι (ZMod 2)), OnWires A p →
    ∀ (c c' : ι → ZMod 2), (∀ i, A i → c i = c' i) → ∀ i, A i → Circuit.run p c i = Circuit.run p c' i
  | [], _, c, c', h, i, hi => h i hi
  | g :: p, hp, c, c', h, i, hi => by
    rw [Circuit.run_cons, Circuit.run_cons]
    apply run_congr_on p (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    have hsum : (g.terms.map fun t => t.2 * c t.1).sum = (g.terms.map fun t => t.2 * c' t.1).sum := by
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [h t.1 (hp g (by simp) t.1 (by
        simp only [FramedCircuit.touched, List.mem_cons, List.mem_map]
        exact Or.inr ⟨t, ht, rfl⟩))]
    simp only [Circuit.Gate.run]
    by_cases hj' : j = g.target
    · subst hj'
      rw [Function.update_self, Function.update_self, hsum, h _ hj]
    · rw [Function.update_of_ne hj', Function.update_of_ne hj', h j hj]
    · exact hi

theorem run_gate_map_on {e : ι → κ} {A : ι → Prop} (he : InjOn' e A) (g : Circuit.Gate ι (ZMod 2))
    (hg : ∀ w ∈ FramedCircuit.touched g, A w) (c : κ → ZMod 2) :
    (∀ i, A i → (gateMap e g).run c (e i) = g.run (c ∘ e) i) ∧
      ∀ k, (∀ i, A i → e i ≠ k) → (gateMap e g).run c k = c k := by
  have htA : A g.target := hg _ (by simp [FramedCircuit.touched])
  have hsum : ((g.terms.map fun t => (e t.1, t.2)).map fun t => t.2 * c t.1).sum =
      (g.terms.map fun t => t.2 * (c ∘ e) t.1).sum := by
    rw [List.map_map]; rfl
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · simp only [gateMap, Circuit.Gate.run, hsum]
    by_cases h : i = g.target
    · subst h; simp
    · rw [Function.update_of_ne (fun h' => h (he _ _ hi htA h')), Function.update_of_ne h]
      rfl
  · simp only [gateMap, Circuit.Gate.run]
    exact Function.update_of_ne (Ne.symm (hk _ htA)) _ _

/-- **Placed programs.** -/
theorem run_map_on {e : ι → κ} {A : ι → Prop} (he : InjOn' e A) :
    ∀ (p : Circuit.Program ι (ZMod 2)), OnWires A p → ∀ (c : κ → ZMod 2),
      (∀ i, A i → Circuit.run (p.map (gateMap e)) c (e i) = Circuit.run p (c ∘ e) i) ∧
        ∀ k, (∀ i, A i → e i ≠ k) → Circuit.run (p.map (gateMap e)) c k = c k
  | [], _, _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | g :: p, hp, c => by
    have hg : ∀ w ∈ FramedCircuit.touched g, A w := hp g (by simp)
    have hp' : OnWires A p := fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')
    obtain ⟨h1, h2⟩ := run_gate_map_on he g hg c
    obtain ⟨ih1, ih2⟩ := run_map_on he p hp' ((gateMap e g).run c)
    refine ⟨fun i hi => ?_, fun k hk => ?_⟩
    · rw [List.map_cons, Circuit.run_cons, ih1 i hi, Circuit.run_cons]
      exact run_congr_on p hp' _ _ (fun j hj => h1 j hj) i hi
    · rw [List.map_cons, Circuit.run_cons, ih2 k hk, h2 k hk]

/-! ### Placed frames -/

/-- Place a framed gate. -/
def placeG (e : ι → κ) (lift : Mat d → Mat d') (v : FGate ι d) : FGate κ d' :=
  ⟨gateMap e v.gate, lift v.frame⟩

theorem fseq_place {e : ι → κ} {A : ι → Prop} (he : InjOn' e A) (lift : Mat d → Mat d')
    (L : List (FGate ι d)) (hL : ∀ v ∈ L, ∀ w ∈ FramedCircuit.touched v.gate, A w) {w : ι}
    (hw : A w) : fseq (e w) (L.map (placeG e lift)) = (fseq w L).map lift := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    rw [List.map_cons, fseq_cons, fseq_cons, ih fun v' hv' => hL v' (List.mem_cons_of_mem _ hv')]
    have hiff : e w ∈ FramedCircuit.touched (placeG e lift v).gate ↔
        w ∈ FramedCircuit.touched v.gate := by
      simp only [placeG, touched_gateMap, List.mem_map]
      constructor
      · rintro ⟨w', hw', he'⟩
        rwa [← he _ _ (hL v (by simp) w' hw') hw he']
      · intro h; exact ⟨w, h, rfl⟩
    by_cases h : w ∈ FramedCircuit.touched v.gate
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

omit [DecidableEq ι] in
theorem fseq_place_out {e : ι → κ} {A : ι → Prop} (lift : Mat d → Mat d')
    (L : List (FGate ι d)) (hL : ∀ v ∈ L, ∀ w ∈ FramedCircuit.touched v.gate, A w) {k : κ}
    (hk : ∀ i, A i → e i ≠ k) : fseq k (L.map (placeG e lift)) = [] := by
  simp only [fseq, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map]
  rintro _ ⟨v, hv, rfl⟩
  simp only [placeG, touched_gateMap, List.mem_map, decide_eq_true_eq, not_exists, not_and]
  intro w hw
  exact hk w (hL v hv w hw)

omit [DecidableEq ι] [DecidableEq κ] in
theorem gatesOk_place {e : ι → κ} {A : ι → Prop} (he : InjOn' e A) (lift : Mat d → Mat d')
    (L : List (FGate ι d)) (hL : ∀ v ∈ L, ∀ w ∈ FramedCircuit.touched v.gate, A w)
    (hx : ∀ v ∈ L, ∃ dst src, dst ≠ src ∧ v.gate = ReversibleFanout.add dst src)
    (hF : ∀ v ∈ L, IsFrame (lift v.frame)) : GatesOk (L.map (placeG e lift)) := by
  intro v' hv'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv'
  refine ⟨hF v hv, ?_⟩
  obtain ⟨dst, src, hne, hg⟩ := hx v hv
  have hd := hL v hv dst (by rw [hg]; simp [FramedCircuit.touched, ReversibleFanout.add])
  have hs := hL v hv src (by rw [hg]; simp [FramedCircuit.touched, ReversibleFanout.add])
  refine ⟨e dst, e src, fun h => hne (he _ _ hd hs h), ?_⟩
  simp [placeG, hg, gateMap, ReversibleFanout.add]

omit [DecidableEq ι] [DecidableEq κ] in
theorem gates_place (e : ι → κ) (lift : Mat d → Mat d') (L : List (FGate ι d)) :
    (L.map (placeG e lift)).map FGate.gate = (L.map FGate.gate).map (gateMap e) := by
  simp [placeG, List.map_map, Function.comp]

end

end IntegerMultBounds.MathlibTM2.M8.Global
