module

public import IntegerMultBounds.MathlibTM2.M8.Frames.RootBankCheck

/-! A basis spans itself, so bank entries used only through their scaled
inverse need no repeated residual checks of their own basis vectors. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootBank

theorem Record.check_self (entry : Record) (h : entry.matrixCheck = true)
    (hgens : entry.generators = entry.basis) : entry.check = true := by
  have hv := h
  simp only [Record.matrixCheck, Bool.and_eq_true] at hv
  apply Bool.and_eq_true_iff.mpr
  refine ⟨h, ?_⟩
  simp only [Record.generatorCheck, hgens]
  apply List.all_eq_true.mpr
  intro g hg
  exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mp hv.1.1 g hg,
    Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr hg))⟩

end IntegerMultBounds.MathlibTM2.M8.Frames.RootBank
