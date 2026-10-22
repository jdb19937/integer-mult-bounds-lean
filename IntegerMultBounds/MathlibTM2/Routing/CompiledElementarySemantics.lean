module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileTableCost
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryInstructionSemantics

/-!
# Coordinate-table semantics of the compiled elementary router

The compiler prepends each emitted frame. Reversing those execution targets
therefore recovers exactly the input table order used by the shear theorem.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem compiledElementary_targets {n : ℕ} (cs : List (ElementaryCoordinate n))
    (ds : List (ElementaryInstruction n))
    (hk : ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key) :
    (ds.map ElementaryInstruction.target).reverse = cs.map ElementaryCoordinate.target := by
  have h := congrArg (fun xs => (xs.map Prod.fst).reverse) hk
  simpa [List.map_map, Function.comp_def, ElementaryCoordinate.key, List.map_reverse] using h

theorem compiledElementary_sources {n : ℕ} (source : Fin n → Fin n)
    (cs : List (ElementaryCoordinate n)) (hc : ∀ c ∈ cs, c.source = source c.target)
    (ds : List (ElementaryInstruction n))
    (hk : ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key) :
    ∀ d ∈ ds, d.source = source d.target := by
  intro d hd
  have hm : (d.target, d.source) ∈ cs.reverse.map ElementaryCoordinate.key := by
    rw [← hk]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨c, hmem, he⟩ := List.mem_map.mp hm
  have ht : c.target = d.target := congrArg Prod.fst he
  have hs : c.source = d.source := congrArg Prod.snd he
  rw [← ht, ← hs]
  exact hc c (List.mem_reverse.mp hmem)

/-- Every output-rank bit is exactly the requested simultaneous shear. -/
theorem compiledElementary_shear {n : ℕ} (rows : ℕ) (targets : Finset (Fin n))
    (source : Fin n → Fin n) (hsource : ∀ i ∈ targets, source i ∉ targets)
    (cs : List (ElementaryCoordinate n)) (hc : ∀ c ∈ cs, c.source = source c.target)
    (ht : cs.map ElementaryCoordinate.target = targets.toList)
    (ds : List (ElementaryInstruction n))
    (hk : ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key)
    (i : Fin (rows * 2 ^ n)) :
    (fun q : Fin n => (elementaryInstructionsRank rows ds i).val.testBit q.val) =
      shear targets source (fun q => i.val.testBit q.val) := by
  exact elementaryInstructionsRank_shear rows targets source hsource ds
    (compiledElementary_sources source cs hc ds hk) ((compiledElementary_targets cs ds hk).trans ht) i

/-- All outer spectator rows survive every generated elementary instruction. -/
theorem compiledElementary_row {n : ℕ} (rows : ℕ) (ds : List (ElementaryInstruction n))
    (i : Fin (rows * 2 ^ n)) :
    (elementaryInstructionsRank rows ds i).val / 2 ^ n = i.val / 2 ^ n := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    change (elementaryInstructionsRank rows ds (d.rank rows i)).val / 2 ^ n = _
    rw [ih]
    exact elementaryXorRank_row d.target d.source d.source_ne rows i

/-- A table covering the shared-geometry suffix has fewer than 131G entries. -/
theorem compiledTerminalTable_count (n G : ℕ) (hG : 0 < G) (hn : 64 * G ≤ n)
    (targets : Finset (Fin (routerTargetWidth n (64 * G) G)))
    (cs : List (ElementaryCoordinate (routerTargetWidth n (64 * G) G)))
    (ht : cs.map ElementaryCoordinate.target = (routerTerminalTargets n (64 * G) G targets).toList) :
    cs.length < 131 * G := by
  have hl := congrArg List.length ht
  simp only [List.length_map, Finset.length_toList] at hl
  rw [hl]
  exact routerTerminalTargets_spacing n G targets hG hn

end IntegerMultBounds.MathlibTM2.Routing
