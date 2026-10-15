module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate048 : Certificate 1 := ⟨48, ![46], ![![0, (1 / 2), (1 / 2), 0, 0, (1 / 2), (1 / 2), 0]]⟩

theorem checked048 : certificate048.Checked := by decide +kernel

theorem dimension048 : Module.finrank ℚ (label 48) = 1 := certificate048.dimension checked048

def certificate049 : Certificate 1 := ⟨49, ![47], ![![0, (1 / 2), (1 / 2), 0, 0, (1 / 2), (-1 / 2), 0]]⟩

theorem checked049 : certificate049.Checked := by decide +kernel

theorem dimension049 : Module.finrank ℚ (label 49) = 1 := certificate049.dimension checked049

def certificate050 : Certificate 1 := ⟨50, ![48], ![![0, (1 / 2), (1 / 2), 0, 0, (-1 / 2), (1 / 2), 0]]⟩

theorem checked050 : certificate050.Checked := by decide +kernel

theorem dimension050 : Module.finrank ℚ (label 50) = 1 := certificate050.dimension checked050

def certificate051 : Certificate 1 := ⟨51, ![49], ![![0, (1 / 2), (-1 / 2), 0, 0, (1 / 2), (1 / 2), 0]]⟩

theorem checked051 : certificate051.Checked := by decide +kernel

theorem dimension051 : Module.finrank ℚ (label 51) = 1 := certificate051.dimension checked051

def certificate052 : Certificate 1 := ⟨52, ![50], ![![0, (1 / 2), (-1 / 2), 0, 0, (-1 / 2), (1 / 2), 0]]⟩

theorem checked052 : certificate052.Checked := by decide +kernel

theorem dimension052 : Module.finrank ℚ (label 52) = 1 := certificate052.dimension checked052

def certificate053 : Certificate 1 := ⟨53, ![51], ![![0, (1 / 2), (-1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0]]⟩

theorem checked053 : certificate053.Checked := by decide +kernel

theorem dimension053 : Module.finrank ℚ (label 53) = 1 := certificate053.dimension checked053

def certificate054 : Certificate 1 := ⟨54, ![52], ![![0, 0, 0, 0, (1 / 2), (1 / 2), (1 / 2), (-1 / 2)]]⟩

theorem checked054 : certificate054.Checked := by decide +kernel

theorem dimension054 : Module.finrank ℚ (label 54) = 1 := certificate054.dimension checked054

def certificate055 : Certificate 1 := ⟨55, ![53], ![![0, 0, 0, 0, (1 / 2), (1 / 2), (-1 / 2), (1 / 2)]]⟩

theorem checked055 : certificate055.Checked := by decide +kernel

theorem dimension055 : Module.finrank ℚ (label 55) = 1 := certificate055.dimension checked055

def certificate056 : Certificate 1 := ⟨56, ![54], ![![0, 0, 0, 0, (1 / 2), (1 / 2), (-1 / 2), (-1 / 2)]]⟩

theorem checked056 : certificate056.Checked := by decide +kernel

theorem dimension056 : Module.finrank ℚ (label 56) = 1 := certificate056.dimension checked056

def certificate057 : Certificate 1 := ⟨57, ![55], ![![0, 0, 0, 0, (1 / 2), (-1 / 2), (1 / 2), (1 / 2)]]⟩

theorem checked057 : certificate057.Checked := by decide +kernel

theorem dimension057 : Module.finrank ℚ (label 57) = 1 := certificate057.dimension checked057

def certificate058 : Certificate 1 := ⟨58, ![56], ![![0, 0, 0, 0, (1 / 2), (-1 / 2), (1 / 2), (-1 / 2)]]⟩

theorem checked058 : certificate058.Checked := by decide +kernel

theorem dimension058 : Module.finrank ℚ (label 58) = 1 := certificate058.dimension checked058

def certificate059 : Certificate 1 := ⟨59, ![57], ![![0, 0, 0, 0, (1 / 2), (-1 / 2), (-1 / 2), (1 / 2)]]⟩

theorem checked059 : certificate059.Checked := by decide +kernel

theorem dimension059 : Module.finrank ℚ (label 59) = 1 := certificate059.dimension checked059

def certificate060 : Certificate 1 := ⟨60, ![58], ![![0, 0, 0, 0, (1 / 2), (-1 / 2), (-1 / 2), (-1 / 2)]]⟩

theorem checked060 : certificate060.Checked := by decide +kernel

theorem dimension060 : Module.finrank ℚ (label 60) = 1 := certificate060.dimension checked060

def certificate061 : Certificate 1 := ⟨61, ![59], ![![(1 / 2), (1 / 2), (1 / 2), (1 / 2), 0, 0, 0, 0]]⟩

theorem checked061 : certificate061.Checked := by decide +kernel

theorem dimension061 : Module.finrank ℚ (label 61) = 1 := certificate061.dimension checked061

def certificate062 : Certificate 1 := ⟨62, ![60], ![![(1 / 2), (1 / 2), (1 / 2), (-1 / 2), 0, 0, 0, 0]]⟩

theorem checked062 : certificate062.Checked := by decide +kernel

theorem dimension062 : Module.finrank ℚ (label 62) = 1 := certificate062.dimension checked062

def certificate063 : Certificate 1 := ⟨63, ![61], ![![(1 / 2), (1 / 2), (-1 / 2), (-1 / 2), 0, 0, 0, 0]]⟩

theorem checked063 : certificate063.Checked := by decide +kernel

theorem dimension063 : Module.finrank ℚ (label 63) = 1 := certificate063.dimension checked063

theorem block003 (i : ℕ) (hl : 48 ≤ i) (hu : i < 64) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension048
  · exact dimension049
  · exact dimension050
  · exact dimension051
  · exact dimension052
  · exact dimension053
  · exact dimension054
  · exact dimension055
  · exact dimension056
  · exact dimension057
  · exact dimension058
  · exact dimension059
  · exact dimension060
  · exact dimension061
  · exact dimension062
  · exact dimension063

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
