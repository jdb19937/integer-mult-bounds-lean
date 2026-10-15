module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate032 : Certificate 1 := ⟨32, ![30], ![![(1 / 2), (1 / 2), 0, 0, (1 / 2), (1 / 2), 0, 0]]⟩

theorem checked032 : certificate032.Checked := by decide +kernel

theorem dimension032 : Module.finrank ℚ (label 32) = 1 := certificate032.dimension checked032

def certificate033 : Certificate 1 := ⟨33, ![31], ![![(1 / 2), (1 / 2), 0, 0, (1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked033 : certificate033.Checked := by decide +kernel

theorem dimension033 : Module.finrank ℚ (label 33) = 1 := certificate033.dimension checked033

def certificate034 : Certificate 1 := ⟨34, ![32], ![![(1 / 2), (1 / 2), 0, 0, (-1 / 2), (1 / 2), 0, 0]]⟩

theorem checked034 : certificate034.Checked := by decide +kernel

theorem dimension034 : Module.finrank ℚ (label 34) = 1 := certificate034.dimension checked034

def certificate035 : Certificate 1 := ⟨35, ![33], ![![(1 / 2), (1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked035 : certificate035.Checked := by decide +kernel

theorem dimension035 : Module.finrank ℚ (label 35) = 1 := certificate035.dimension checked035

def certificate036 : Certificate 1 := ⟨36, ![34], ![![(1 / 2), (-1 / 2), 0, 0, (1 / 2), (1 / 2), 0, 0]]⟩

theorem checked036 : certificate036.Checked := by decide +kernel

theorem dimension036 : Module.finrank ℚ (label 36) = 1 := certificate036.dimension checked036

def certificate037 : Certificate 1 := ⟨37, ![35], ![![(1 / 2), (-1 / 2), 0, 0, (1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked037 : certificate037.Checked := by decide +kernel

theorem dimension037 : Module.finrank ℚ (label 37) = 1 := certificate037.dimension checked037

def certificate038 : Certificate 1 := ⟨38, ![36], ![![(1 / 2), (-1 / 2), 0, 0, (-1 / 2), (1 / 2), 0, 0]]⟩

theorem checked038 : certificate038.Checked := by decide +kernel

theorem dimension038 : Module.finrank ℚ (label 38) = 1 := certificate038.dimension checked038

def certificate039 : Certificate 1 := ⟨39, ![37], ![![(1 / 2), (-1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked039 : certificate039.Checked := by decide +kernel

theorem dimension039 : Module.finrank ℚ (label 39) = 1 := certificate039.dimension checked039

def certificate040 : Certificate 1 := ⟨40, ![38], ![![(1 / 2), 0, (1 / 2), 0, 0, (1 / 2), 0, (1 / 2)]]⟩

theorem checked040 : certificate040.Checked := by decide +kernel

theorem dimension040 : Module.finrank ℚ (label 40) = 1 := certificate040.dimension checked040

def certificate041 : Certificate 1 := ⟨41, ![39], ![![(1 / 2), 0, (1 / 2), 0, 0, (1 / 2), 0, (-1 / 2)]]⟩

theorem checked041 : certificate041.Checked := by decide +kernel

theorem dimension041 : Module.finrank ℚ (label 41) = 1 := certificate041.dimension checked041

def certificate042 : Certificate 1 := ⟨42, ![40], ![![(1 / 2), 0, (1 / 2), 0, 0, (-1 / 2), 0, (1 / 2)]]⟩

theorem checked042 : certificate042.Checked := by decide +kernel

theorem dimension042 : Module.finrank ℚ (label 42) = 1 := certificate042.dimension checked042

def certificate043 : Certificate 1 := ⟨43, ![41], ![![(1 / 2), 0, (1 / 2), 0, 0, (-1 / 2), 0, (-1 / 2)]]⟩

theorem checked043 : certificate043.Checked := by decide +kernel

theorem dimension043 : Module.finrank ℚ (label 43) = 1 := certificate043.dimension checked043

def certificate044 : Certificate 1 := ⟨44, ![42], ![![(1 / 2), 0, (-1 / 2), 0, 0, (1 / 2), 0, (1 / 2)]]⟩

theorem checked044 : certificate044.Checked := by decide +kernel

theorem dimension044 : Module.finrank ℚ (label 44) = 1 := certificate044.dimension checked044

def certificate045 : Certificate 1 := ⟨45, ![43], ![![(1 / 2), 0, (-1 / 2), 0, 0, (1 / 2), 0, (-1 / 2)]]⟩

theorem checked045 : certificate045.Checked := by decide +kernel

theorem dimension045 : Module.finrank ℚ (label 45) = 1 := certificate045.dimension checked045

def certificate046 : Certificate 1 := ⟨46, ![44], ![![(1 / 2), 0, (-1 / 2), 0, 0, (-1 / 2), 0, (1 / 2)]]⟩

theorem checked046 : certificate046.Checked := by decide +kernel

theorem dimension046 : Module.finrank ℚ (label 46) = 1 := certificate046.dimension checked046

def certificate047 : Certificate 1 := ⟨47, ![45], ![![(1 / 2), 0, (-1 / 2), 0, 0, (-1 / 2), 0, (-1 / 2)]]⟩

theorem checked047 : certificate047.Checked := by decide +kernel

theorem dimension047 : Module.finrank ℚ (label 47) = 1 := certificate047.dimension checked047

theorem block002 (i : ℕ) (hl : 32 ≤ i) (hu : i < 48) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension032
  · exact dimension033
  · exact dimension034
  · exact dimension035
  · exact dimension036
  · exact dimension037
  · exact dimension038
  · exact dimension039
  · exact dimension040
  · exact dimension041
  · exact dimension042
  · exact dimension043
  · exact dimension044
  · exact dimension045
  · exact dimension046
  · exact dimension047

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
