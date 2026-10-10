import IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge

/-! Chronological recursive calls agree with the original frame product.
Commutativity comes from the actual column translation kernels, including
calls acting on the same column, rather than an extra scheduling premise. -/
namespace IntegerMultBounds.Machine.CompactComplexActualCallOrder
noncomputable section
open Networks
open BinaryColumns
open CompactComplexActualCallFrameEdge (kernel)
open ComplexRecursiveCallSchema (Call Occurrence callsAt edge)
variable {h columns : ℕ}

theorem vectorFactor_commute (g t : ZMod 4 × BinaryWalsh.Address h) :
    Commute (vectorFactor columns g) (vectorFactor columns t) := by
  unfold vectorFactor
  apply Commute.list_prod_left
  intro T hT
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hT
  apply Commute.list_prod_right
  intro S hS
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hS
  exact columnKernel_commute i j g.1 t.1 g.2 t.2

/-- Reversing any literal direction list preserves its actual array product. -/
theorem reverse_factor_product (gs : List (ZMod 4 × BinaryWalsh.Address h)) :
    (gs.reverse.map (vectorFactor columns)).prod=(gs.map (vectorFactor columns)).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.prod_append,List.prod_cons,List.prod_nil,mul_one,ih]
    exact (Commute.list_prod_right (gs.map (vectorFactor columns)) (vectorFactor columns g)
      (by intro T hT; obtain ⟨t,_ht,rfl⟩ := List.mem_map.mp hT
          exact vectorFactor_commute g t)).symm.eq

/-- Ordinary left-to-right call execution evaluates the reverse End product. -/
theorem foldl_factor_reverse (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : Arrays h columns) :
    gs.foldl (fun state g => vectorFactor columns g state) f=
      (gs.reverse.map (vectorFactor columns)).prod f := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,List.reverse_cons,List.map_append,List.map_cons,
      List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one]
    rfl

/-- Actual chronological factors compute the same literal product as the
original rational frame edge, without reversing the physical call order. -/
theorem chronological_factor_product (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : Arrays h columns) :
    gs.foldl (fun state g => vectorFactor columns g state) f=
      (gs.map (vectorFactor columns)).prod f := by
  rw [foldl_factor_reverse,reverse_factor_product]

/-- Literal call occurrence order agrees with the original edge transition. -/
theorem calls_frame_edge (site : Occurrence) (f : Arrays (25^3) columns) :
    (callsAt site).foldl (fun state call => vectorFactor columns (kernel call) state) f=
      ComplexFramedExecution.frameOf columns (edge site).val.2
        ((ComplexFramedExecution.frameOf columns (edge site).val.1).symm f) := by
  rw [←List.foldl_map (f:=kernel) (g:=fun state g => vectorFactor columns g state)]
  exact (chronological_factor_product ((callsAt site).map kernel) f).trans
    (CompactComplexActualCallFrameEdge.original_frame_call_product columns site f).symm

end
end IntegerMultBounds.Machine.CompactComplexActualCallOrder
