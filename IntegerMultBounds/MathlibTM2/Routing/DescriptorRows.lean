module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryMaskEmit
public import IntegerMultBounds.MathlibTM2.Routing.ReadPattern

/-! The generated one-hot rows are exactly the actual descriptor interpreter's
input format, including the zero selector for absent pattern entries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

theorem sourceTable_binSyms {A W : ℕ} (indices : List (Fin W)) :
    (sourceTable indices).flatten.map (bitSymbol (a := A)) =
      (indices.map (fun q => binSyms W (2 ^ q.val))).flatten := by
  unfold sourceTable
  rw [List.map_flatten]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  exact (binSyms_oneHot q).symm

theorem patternTable_binSyms {A W L : ℕ} (s : Fin L → Option (Fin W)) :
    (patternTable s).flatten.map (bitSymbol (a := A)) =
      (List.ofFn (fun j => binSyms (W + 1) (2 ^ (patternIndex s j).val))).flatten := by
  rw [patternTable, sourceTable_binSyms, List.map_ofFn]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
