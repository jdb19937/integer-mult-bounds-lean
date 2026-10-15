module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate080 : Certificate 1 := ⟨80, ![78], ![![0, (1 / 2), 0, (-1 / 2), (1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked080 : certificate080.Checked := by decide +kernel

theorem dimension080 : Module.finrank ℚ (label 80) = 1 := certificate080.dimension checked080

def certificate081 : Certificate 1 := ⟨81, ![79], ![![0, (1 / 2), 0, (-1 / 2), (-1 / 2), 0, (1 / 2), 0]]⟩

theorem checked081 : certificate081.Checked := by decide +kernel

theorem dimension081 : Module.finrank ℚ (label 81) = 1 := certificate081.dimension checked081

def certificate082 : Certificate 1 := ⟨82, ![80], ![![0, (1 / 2), 0, (-1 / 2), (-1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked082 : certificate082.Checked := by decide +kernel

theorem dimension082 : Module.finrank ℚ (label 82) = 1 := certificate082.dimension checked082

def certificate083 : Certificate 1 := ⟨83, ![81], ![![0, 0, (1 / 2), (1 / 2), 0, 0, (1 / 2), (1 / 2)]]⟩

theorem checked083 : certificate083.Checked := by decide +kernel

theorem dimension083 : Module.finrank ℚ (label 83) = 1 := certificate083.dimension checked083

def certificate084 : Certificate 1 := ⟨84, ![82], ![![0, 0, (1 / 2), (1 / 2), 0, 0, (-1 / 2), (1 / 2)]]⟩

theorem checked084 : certificate084.Checked := by decide +kernel

theorem dimension084 : Module.finrank ℚ (label 84) = 1 := certificate084.dimension checked084

def certificate085 : Certificate 1 := ⟨85, ![83], ![![0, 0, (1 / 2), (1 / 2), 0, 0, (-1 / 2), (-1 / 2)]]⟩

theorem checked085 : certificate085.Checked := by decide +kernel

theorem dimension085 : Module.finrank ℚ (label 85) = 1 := certificate085.dimension checked085

def certificate086 : Certificate 1 := ⟨86, ![84], ![![0, 0, (1 / 2), (-1 / 2), 0, 0, (1 / 2), (1 / 2)]]⟩

theorem checked086 : certificate086.Checked := by decide +kernel

theorem dimension086 : Module.finrank ℚ (label 86) = 1 := certificate086.dimension checked086

def certificate087 : Certificate 1 := ⟨87, ![85], ![![0, 0, (1 / 2), (-1 / 2), 0, 0, (1 / 2), (-1 / 2)]]⟩

theorem checked087 : certificate087.Checked := by decide +kernel

theorem dimension087 : Module.finrank ℚ (label 87) = 1 := certificate087.dimension checked087

def certificate088 : Certificate 1 := ⟨88, ![86], ![![0, 0, (1 / 2), (-1 / 2), 0, 0, (-1 / 2), (1 / 2)]]⟩

theorem checked088 : certificate088.Checked := by decide +kernel

theorem dimension088 : Module.finrank ℚ (label 88) = 1 := certificate088.dimension checked088

def certificate089 : Certificate 1 := ⟨89, ![87], ![![0, 0, (1 / 2), (-1 / 2), 0, 0, (-1 / 2), (-1 / 2)]]⟩

theorem checked089 : certificate089.Checked := by decide +kernel

theorem dimension089 : Module.finrank ℚ (label 89) = 1 := certificate089.dimension checked089

def certificate090 : Certificate 1 := ⟨90, ![88], ![![0, 0, (1 / 2), (1 / 2), (1 / 2), (1 / 2), 0, 0]]⟩

theorem checked090 : certificate090.Checked := by decide +kernel

theorem dimension090 : Module.finrank ℚ (label 90) = 1 := certificate090.dimension checked090

def certificate091 : Certificate 1 := ⟨91, ![89], ![![0, 0, (1 / 2), (1 / 2), (1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked091 : certificate091.Checked := by decide +kernel

theorem dimension091 : Module.finrank ℚ (label 91) = 1 := certificate091.dimension checked091

def certificate092 : Certificate 1 := ⟨92, ![90], ![![0, 0, (1 / 2), (1 / 2), (-1 / 2), (1 / 2), 0, 0]]⟩

theorem checked092 : certificate092.Checked := by decide +kernel

theorem dimension092 : Module.finrank ℚ (label 92) = 1 := certificate092.dimension checked092

def certificate093 : Certificate 1 := ⟨93, ![91], ![![0, 0, (1 / 2), (1 / 2), (-1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked093 : certificate093.Checked := by decide +kernel

theorem dimension093 : Module.finrank ℚ (label 93) = 1 := certificate093.dimension checked093

def certificate094 : Certificate 1 := ⟨94, ![92], ![![0, 0, (1 / 2), (-1 / 2), (1 / 2), (1 / 2), 0, 0]]⟩

theorem checked094 : certificate094.Checked := by decide +kernel

theorem dimension094 : Module.finrank ℚ (label 94) = 1 := certificate094.dimension checked094

def certificate095 : Certificate 1 := ⟨95, ![93], ![![0, 0, (1 / 2), (-1 / 2), (1 / 2), (-1 / 2), 0, 0]]⟩

theorem checked095 : certificate095.Checked := by decide +kernel

theorem dimension095 : Module.finrank ℚ (label 95) = 1 := certificate095.dimension checked095

theorem block005 (i : ℕ) (hl : 80 ≤ i) (hu : i < 96) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension080
  · exact dimension081
  · exact dimension082
  · exact dimension083
  · exact dimension084
  · exact dimension085
  · exact dimension086
  · exact dimension087
  · exact dimension088
  · exact dimension089
  · exact dimension090
  · exact dimension091
  · exact dimension092
  · exact dimension093
  · exact dimension094
  · exact dimension095

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
