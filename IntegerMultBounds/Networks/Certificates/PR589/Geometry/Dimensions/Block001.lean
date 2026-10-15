module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

def certificate016 : Certificate 1 := ⟨16, ![14], ![![(1 / 2), 0, (1 / 2), 0, (1 / 2), 0, (1 / 2), 0]]⟩

theorem checked016 : certificate016.Checked := by decide +kernel

theorem dimension016 : Module.finrank ℚ (label 16) = 1 := certificate016.dimension checked016

def certificate017 : Certificate 1 := ⟨17, ![15], ![![(1 / 2), 0, (1 / 2), 0, (1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked017 : certificate017.Checked := by decide +kernel

theorem dimension017 : Module.finrank ℚ (label 17) = 1 := certificate017.dimension checked017

def certificate018 : Certificate 1 := ⟨18, ![16], ![![(1 / 2), 0, (1 / 2), 0, (-1 / 2), 0, (1 / 2), 0]]⟩

theorem checked018 : certificate018.Checked := by decide +kernel

theorem dimension018 : Module.finrank ℚ (label 18) = 1 := certificate018.dimension checked018

def certificate019 : Certificate 1 := ⟨19, ![17], ![![(1 / 2), 0, (1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked019 : certificate019.Checked := by decide +kernel

theorem dimension019 : Module.finrank ℚ (label 19) = 1 := certificate019.dimension checked019

def certificate020 : Certificate 1 := ⟨20, ![18], ![![(1 / 2), 0, (-1 / 2), 0, (1 / 2), 0, (1 / 2), 0]]⟩

theorem checked020 : certificate020.Checked := by decide +kernel

theorem dimension020 : Module.finrank ℚ (label 20) = 1 := certificate020.dimension checked020

def certificate021 : Certificate 1 := ⟨21, ![19], ![![(1 / 2), 0, (-1 / 2), 0, (1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked021 : certificate021.Checked := by decide +kernel

theorem dimension021 : Module.finrank ℚ (label 21) = 1 := certificate021.dimension checked021

def certificate022 : Certificate 1 := ⟨22, ![20], ![![(1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0, (1 / 2), 0]]⟩

theorem checked022 : certificate022.Checked := by decide +kernel

theorem dimension022 : Module.finrank ℚ (label 22) = 1 := certificate022.dimension checked022

def certificate023 : Certificate 1 := ⟨23, ![21], ![![(1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0]]⟩

theorem checked023 : certificate023.Checked := by decide +kernel

theorem dimension023 : Module.finrank ℚ (label 23) = 1 := certificate023.dimension checked023

def certificate024 : Certificate 1 := ⟨24, ![22], ![![(1 / 2), (1 / 2), 0, 0, 0, 0, (1 / 2), (1 / 2)]]⟩

theorem checked024 : certificate024.Checked := by decide +kernel

theorem dimension024 : Module.finrank ℚ (label 24) = 1 := certificate024.dimension checked024

def certificate025 : Certificate 1 := ⟨25, ![23], ![![(1 / 2), (1 / 2), 0, 0, 0, 0, (1 / 2), (-1 / 2)]]⟩

theorem checked025 : certificate025.Checked := by decide +kernel

theorem dimension025 : Module.finrank ℚ (label 25) = 1 := certificate025.dimension checked025

def certificate026 : Certificate 1 := ⟨26, ![24], ![![(1 / 2), (1 / 2), 0, 0, 0, 0, (-1 / 2), (1 / 2)]]⟩

theorem checked026 : certificate026.Checked := by decide +kernel

theorem dimension026 : Module.finrank ℚ (label 26) = 1 := certificate026.dimension checked026

def certificate027 : Certificate 1 := ⟨27, ![25], ![![(1 / 2), (1 / 2), 0, 0, 0, 0, (-1 / 2), (-1 / 2)]]⟩

theorem checked027 : certificate027.Checked := by decide +kernel

theorem dimension027 : Module.finrank ℚ (label 27) = 1 := certificate027.dimension checked027

def certificate028 : Certificate 1 := ⟨28, ![26], ![![(1 / 2), (-1 / 2), 0, 0, 0, 0, (1 / 2), (1 / 2)]]⟩

theorem checked028 : certificate028.Checked := by decide +kernel

theorem dimension028 : Module.finrank ℚ (label 28) = 1 := certificate028.dimension checked028

def certificate029 : Certificate 1 := ⟨29, ![27], ![![(1 / 2), (-1 / 2), 0, 0, 0, 0, (1 / 2), (-1 / 2)]]⟩

theorem checked029 : certificate029.Checked := by decide +kernel

theorem dimension029 : Module.finrank ℚ (label 29) = 1 := certificate029.dimension checked029

def certificate030 : Certificate 1 := ⟨30, ![28], ![![(1 / 2), (-1 / 2), 0, 0, 0, 0, (-1 / 2), (1 / 2)]]⟩

theorem checked030 : certificate030.Checked := by decide +kernel

theorem dimension030 : Module.finrank ℚ (label 30) = 1 := certificate030.dimension checked030

def certificate031 : Certificate 1 := ⟨31, ![29], ![![(1 / 2), (-1 / 2), 0, 0, 0, 0, (-1 / 2), (-1 / 2)]]⟩

theorem checked031 : certificate031.Checked := by decide +kernel

theorem dimension031 : Module.finrank ℚ (label 31) = 1 := certificate031.dimension checked031

theorem block001 (i : ℕ) (hl : 16 ≤ i) (hu : i < 32) :
    Module.finrank ℚ (label i) = value i := by
  interval_cases i
  · exact dimension016
  · exact dimension017
  · exact dimension018
  · exact dimension019
  · exact dimension020
  · exact dimension021
  · exact dimension022
  · exact dimension023
  · exact dimension024
  · exact dimension025
  · exact dimension026
  · exact dimension027
  · exact dimension028
  · exact dimension029
  · exact dimension030
  · exact dimension031

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
