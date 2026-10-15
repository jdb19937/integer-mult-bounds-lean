module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate064 : Certificate 1 := ⟨64, ![62], ![![(1 / 2), (-1 / 2), (1 / 2), (1 / 2), 0, 0, 0, 0]]⟩

theorem checked064 : certificate064.Checked := by decide +kernel

theorem dimension064 : Module.finrank ℚ (label 64) = 1 := certificate064.dimension checked064

def certificate065 : Certificate 1 := ⟨65, ![63], ![![(1 / 2), (-1 / 2), (1 / 2), (-1 / 2), 0, 0, 0, 0]]⟩

theorem checked065 : certificate065.Checked := by decide +kernel

theorem dimension065 : Module.finrank ℚ (label 65) = 1 := certificate065.dimension checked065

def certificate066 : Certificate 1 := ⟨66, ![64], ![![(1 / 2), (-1 / 2), (-1 / 2), (1 / 2), 0, 0, 0, 0]]⟩

theorem checked066 : certificate066.Checked := by decide +kernel

theorem dimension066 : Module.finrank ℚ (label 66) = 1 := certificate066.dimension checked066

def certificate067 : Certificate 1 := ⟨67, ![65], ![![(1 / 2), (-1 / 2), (-1 / 2), (-1 / 2), 0, 0, 0, 0]]⟩

theorem checked067 : certificate067.Checked := by decide +kernel

theorem dimension067 : Module.finrank ℚ (label 67) = 1 := certificate067.dimension checked067

def certificate068 : Certificate 1 := ⟨68, ![66], ![![(1 / 2), 0, 0, (1 / 2), (1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked068 : certificate068.Checked := by decide +kernel

theorem dimension068 : Module.finrank ℚ (label 68) = 1 := certificate068.dimension checked068

def certificate069 : Certificate 1 := ⟨69, ![67], ![![(1 / 2), 0, 0, (1 / 2), (-1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked069 : certificate069.Checked := by decide +kernel

theorem dimension069 : Module.finrank ℚ (label 69) = 1 := certificate069.dimension checked069

def certificate070 : Certificate 1 := ⟨70, ![68], ![![(1 / 2), 0, 0, (1 / 2), (-1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked070 : certificate070.Checked := by decide +kernel

theorem dimension070 : Module.finrank ℚ (label 70) = 1 := certificate070.dimension checked070

def certificate071 : Certificate 1 := ⟨71, ![69], ![![(1 / 2), 0, 0, (-1 / 2), (1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked071 : certificate071.Checked := by decide +kernel

theorem dimension071 : Module.finrank ℚ (label 71) = 1 := certificate071.dimension checked071

def certificate072 : Certificate 1 := ⟨72, ![70], ![![(1 / 2), 0, 0, (-1 / 2), (1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked072 : certificate072.Checked := by decide +kernel

theorem dimension072 : Module.finrank ℚ (label 72) = 1 := certificate072.dimension checked072

def certificate073 : Certificate 1 := ⟨73, ![71], ![![(1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked073 : certificate073.Checked := by decide +kernel

theorem dimension073 : Module.finrank ℚ (label 73) = 1 := certificate073.dimension checked073

def certificate074 : Certificate 1 := ⟨74, ![72], ![![(1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked074 : certificate074.Checked := by decide +kernel

theorem dimension074 : Module.finrank ℚ (label 74) = 1 := certificate074.dimension checked074

def certificate075 : Certificate 1 := ⟨75, ![73], ![![0, (1 / 2), 0, (1 / 2), (1 / 2), 0, (1 / 2), 0]]⟩

theorem checked075 : certificate075.Checked := by decide +kernel

theorem dimension075 : Module.finrank ℚ (label 75) = 1 := certificate075.dimension checked075

def certificate076 : Certificate 1 := ⟨76, ![74], ![![0, (1 / 2), 0, (1 / 2), (1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked076 : certificate076.Checked := by decide +kernel

theorem dimension076 : Module.finrank ℚ (label 76) = 1 := certificate076.dimension checked076

def certificate077 : Certificate 1 := ⟨77, ![75], ![![0, (1 / 2), 0, (1 / 2), (-1 / 2), 0, (1 / 2), 0]]⟩

theorem checked077 : certificate077.Checked := by decide +kernel

theorem dimension077 : Module.finrank ℚ (label 77) = 1 := certificate077.dimension checked077

def certificate078 : Certificate 1 := ⟨78, ![76], ![![0, (1 / 2), 0, (1 / 2), (-1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked078 : certificate078.Checked := by decide +kernel

theorem dimension078 : Module.finrank ℚ (label 78) = 1 := certificate078.dimension checked078

def certificate079 : Certificate 1 := ⟨79, ![77], ![![0, (1 / 2), 0, (-1 / 2), (1 / 2), 0, (1 / 2), 0]]⟩

theorem checked079 : certificate079.Checked := by decide +kernel

theorem dimension079 : Module.finrank ℚ (label 79) = 1 := certificate079.dimension checked079

theorem block004 (i : ℕ) (hl : 64 ≤ i) (hu : i < 80) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension064
  · exact dimension065
  · exact dimension066
  · exact dimension067
  · exact dimension068
  · exact dimension069
  · exact dimension070
  · exact dimension071
  · exact dimension072
  · exact dimension073
  · exact dimension074
  · exact dimension075
  · exact dimension076
  · exact dimension077
  · exact dimension078
  · exact dimension079

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
