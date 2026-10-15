module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate000 : Certificate 0 := ⟨0, Fin.elim0, Fin.elim0⟩

theorem checked000 : certificate000.Checked := by decide +kernel

theorem dimension000 : Module.finrank ℚ (label 0) = 0 := certificate000.dimension checked000

def certificate001 : Certificate 8 := ⟨1, ![0, 1, 2, 3, 4, 5, 6, 7], ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]⟩

theorem checked001 : certificate001.Checked := by decide +kernel

theorem dimension001 : Module.finrank ℚ (label 1) = 8 := certificate001.dimension checked001

def certificate002 : Certificate 1 := ⟨2, ![0], ![![1, 0, 0, 0, 0, 0, 0, 0]]⟩

theorem checked002 : certificate002.Checked := by decide +kernel

theorem dimension002 : Module.finrank ℚ (label 2) = 1 := certificate002.dimension checked002

def certificate003 : Certificate 1 := ⟨3, ![1], ![![0, 1, 0, 0, 0, 0, 0, 0]]⟩

theorem checked003 : certificate003.Checked := by decide +kernel

theorem dimension003 : Module.finrank ℚ (label 3) = 1 := certificate003.dimension checked003

def certificate004 : Certificate 1 := ⟨4, ![2], ![![0, 0, 1, 0, 0, 0, 0, 0]]⟩

theorem checked004 : certificate004.Checked := by decide +kernel

theorem dimension004 : Module.finrank ℚ (label 4) = 1 := certificate004.dimension checked004

def certificate005 : Certificate 1 := ⟨5, ![3], ![![0, 0, 0, 1, 0, 0, 0, 0]]⟩

theorem checked005 : certificate005.Checked := by decide +kernel

theorem dimension005 : Module.finrank ℚ (label 5) = 1 := certificate005.dimension checked005

def certificate006 : Certificate 1 := ⟨6, ![4], ![![0, 0, 0, 0, 1, 0, 0, 0]]⟩

theorem checked006 : certificate006.Checked := by decide +kernel

theorem dimension006 : Module.finrank ℚ (label 6) = 1 := certificate006.dimension checked006

def certificate007 : Certificate 1 := ⟨7, ![5], ![![0, 0, 0, 0, 0, 1, 0, 0]]⟩

theorem checked007 : certificate007.Checked := by decide +kernel

theorem dimension007 : Module.finrank ℚ (label 7) = 1 := certificate007.dimension checked007

def certificate008 : Certificate 1 := ⟨8, ![6], ![![0, 0, 0, 0, 0, 0, 1, 0]]⟩

theorem checked008 : certificate008.Checked := by decide +kernel

theorem dimension008 : Module.finrank ℚ (label 8) = 1 := certificate008.dimension checked008

def certificate009 : Certificate 1 := ⟨9, ![7], ![![0, 0, 0, 0, 0, 0, 0, 1]]⟩

theorem checked009 : certificate009.Checked := by decide +kernel

theorem dimension009 : Module.finrank ℚ (label 9) = 1 := certificate009.dimension checked009

def certificate010 : Certificate 1 := ⟨10, ![8], ![![0, (1 / 2), (1 / 2), 0, (1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked010 : certificate010.Checked := by decide +kernel

theorem dimension010 : Module.finrank ℚ (label 10) = 1 := certificate010.dimension checked010

def certificate011 : Certificate 1 := ⟨11, ![9], ![![0, (1 / 2), (1 / 2), 0, (1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked011 : certificate011.Checked := by decide +kernel

theorem dimension011 : Module.finrank ℚ (label 11) = 1 := certificate011.dimension checked011

def certificate012 : Certificate 1 := ⟨12, ![10], ![![0, (1 / 2), (1 / 2), 0, (-1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked012 : certificate012.Checked := by decide +kernel

theorem dimension012 : Module.finrank ℚ (label 12) = 1 := certificate012.dimension checked012

def certificate013 : Certificate 1 := ⟨13, ![11], ![![0, (1 / 2), (-1 / 2), 0, (1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked013 : certificate013.Checked := by decide +kernel

theorem dimension013 : Module.finrank ℚ (label 13) = 1 := certificate013.dimension checked013

def certificate014 : Certificate 1 := ⟨14, ![12], ![![0, (1 / 2), (-1 / 2), 0, (1 / 2), 0, 0, (-1 / 2)]]⟩

theorem checked014 : certificate014.Checked := by decide +kernel

theorem dimension014 : Module.finrank ℚ (label 14) = 1 := certificate014.dimension checked014

def certificate015 : Certificate 1 := ⟨15, ![13], ![![0, (1 / 2), (-1 / 2), 0, (-1 / 2), 0, 0, (1 / 2)]]⟩

theorem checked015 : certificate015.Checked := by decide +kernel

theorem dimension015 : Module.finrank ℚ (label 15) = 1 := certificate015.dimension checked015

theorem block000 (i : ℕ) (hl : 0 ≤ i) (hu : i < 16) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension000
  · exact dimension001
  · exact dimension002
  · exact dimension003
  · exact dimension004
  · exact dimension005
  · exact dimension006
  · exact dimension007
  · exact dimension008
  · exact dimension009
  · exact dimension010
  · exact dimension011
  · exact dimension012
  · exact dimension013
  · exact dimension014
  · exact dimension015

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
