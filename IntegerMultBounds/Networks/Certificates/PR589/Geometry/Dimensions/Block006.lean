module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate096 : Certificate 1 := ⟨96, ![94], ![![0, 0, (1 / 2), (-1 / 2), (-1 / 2), (1 / 2), 0, 0]]⟩

theorem checked096 : certificate096.Checked := by decide +kernel

theorem dimension096 : Module.finrank ℚ (label 96) = 1 := certificate096.dimension checked096

def certificate097 : Certificate 1 := ⟨97, ![95], ![![0, 0, (1 / 2), (-1 / 2), (-1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked097 : certificate097.Checked := by decide +kernel

theorem dimension097 : Module.finrank ℚ (label 97) = 1 := certificate097.dimension checked097

def certificate098 : Certificate 1 := ⟨98, ![96], ![![0, (1 / 2), 0, (1 / 2), 0, (1 / 2), 0, (1 / 2)]]⟩

theorem checked098 : certificate098.Checked := by decide +kernel

theorem dimension098 : Module.finrank ℚ (label 98) = 1 := certificate098.dimension checked098

def certificate099 : Certificate 1 := ⟨99, ![97], ![![0, (1 / 2), 0, (1 / 2), 0, (1 / 2), 0, (-1 / 2)]]⟩

theorem checked099 : certificate099.Checked := by decide +kernel

theorem dimension099 : Module.finrank ℚ (label 99) = 1 := certificate099.dimension checked099

def certificate100 : Certificate 1 := ⟨100, ![98], ![![0, (1 / 2), 0, (1 / 2), 0, (-1 / 2), 0, (1 / 2)]]⟩

theorem checked100 : certificate100.Checked := by decide +kernel

theorem dimension100 : Module.finrank ℚ (label 100) = 1 := certificate100.dimension checked100

def certificate101 : Certificate 1 := ⟨101, ![99], ![![0, (1 / 2), 0, (1 / 2), 0, (-1 / 2), 0, (-1 / 2)]]⟩

theorem checked101 : certificate101.Checked := by decide +kernel

theorem dimension101 : Module.finrank ℚ (label 101) = 1 := certificate101.dimension checked101

def certificate102 : Certificate 1 := ⟨102, ![100], ![![0, (1 / 2), 0, (-1 / 2), 0, (1 / 2), 0, (1 / 2)]]⟩

theorem checked102 : certificate102.Checked := by decide +kernel

theorem dimension102 : Module.finrank ℚ (label 102) = 1 := certificate102.dimension checked102

def certificate103 : Certificate 1 := ⟨103, ![101], ![![0, (1 / 2), 0, (-1 / 2), 0, (1 / 2), 0, (-1 / 2)]]⟩

theorem checked103 : certificate103.Checked := by decide +kernel

theorem dimension103 : Module.finrank ℚ (label 103) = 1 := certificate103.dimension checked103

def certificate104 : Certificate 1 := ⟨104, ![102], ![![0, (1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0, (1 / 2)]]⟩

theorem checked104 : certificate104.Checked := by decide +kernel

theorem dimension104 : Module.finrank ℚ (label 104) = 1 := certificate104.dimension checked104

def certificate105 : Certificate 1 := ⟨105, ![103], ![![(1 / 2), 0, 0, (1 / 2), 0, (1 / 2), (1 / 2), 0]]⟩

theorem checked105 : certificate105.Checked := by decide +kernel

theorem dimension105 : Module.finrank ℚ (label 105) = 1 := certificate105.dimension checked105

def certificate106 : Certificate 1 := ⟨106, ![104], ![![(1 / 2), 0, 0, (1 / 2), 0, (1 / 2), (-1 / 2), 0]]⟩

theorem checked106 : certificate106.Checked := by decide +kernel

theorem dimension106 : Module.finrank ℚ (label 106) = 1 := certificate106.dimension checked106

def certificate107 : Certificate 1 := ⟨107, ![105], ![![(1 / 2), 0, 0, (1 / 2), 0, (-1 / 2), (1 / 2), 0]]⟩

theorem checked107 : certificate107.Checked := by decide +kernel

theorem dimension107 : Module.finrank ℚ (label 107) = 1 := certificate107.dimension checked107

def certificate108 : Certificate 1 := ⟨108, ![106], ![![(1 / 2), 0, 0, (1 / 2), 0, (-1 / 2), (-1 / 2), 0]]⟩

theorem checked108 : certificate108.Checked := by decide +kernel

theorem dimension108 : Module.finrank ℚ (label 108) = 1 := certificate108.dimension checked108

def certificate109 : Certificate 1 := ⟨109, ![107], ![![(1 / 2), 0, 0, (-1 / 2), 0, (1 / 2), (1 / 2), 0]]⟩

theorem checked109 : certificate109.Checked := by decide +kernel

theorem dimension109 : Module.finrank ℚ (label 109) = 1 := certificate109.dimension checked109

def certificate110 : Certificate 1 := ⟨110, ![108], ![![(1 / 2), 0, 0, (-1 / 2), 0, (1 / 2), (-1 / 2), 0]]⟩

theorem checked110 : certificate110.Checked := by decide +kernel

theorem dimension110 : Module.finrank ℚ (label 110) = 1 := certificate110.dimension checked110

def certificate111 : Certificate 1 := ⟨111, ![109], ![![(1 / 2), 0, 0, (-1 / 2), 0, (-1 / 2), (1 / 2), 0]]⟩

theorem checked111 : certificate111.Checked := by decide +kernel

theorem dimension111 : Module.finrank ℚ (label 111) = 1 := certificate111.dimension checked111

theorem block006 (i : ℕ) (hl : 96 ≤ i) (hu : i < 112) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension096
  · exact dimension097
  · exact dimension098
  · exact dimension099
  · exact dimension100
  · exact dimension101
  · exact dimension102
  · exact dimension103
  · exact dimension104
  · exact dimension105
  · exact dimension106
  · exact dimension107
  · exact dimension108
  · exact dimension109
  · exact dimension110
  · exact dimension111

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
