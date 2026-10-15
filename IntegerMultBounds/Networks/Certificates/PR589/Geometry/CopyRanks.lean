module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.RankCertificate

/-! Generated exact rational witnesses. Lean checks every membership, dual pairing
and normal equation; dimensions are derived from those checks, not imported. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry

def certificate510 : HyperplaneCertificate :=
  ⟨510, ![0, 3, 5, 6, 9, 11, 14], ![![1, (1 / 2), (-1 / 2), 0, (-1 / 2), 0, 0, (-1 / 2)], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, (1 / 2), (-1 / 2), 0, (-1 / 2), 0, 1, (-1 / 2)], ![0, 1, 0, 0, 0, 0, 0, -1], ![0, (1 / 2), (-1 / 2), 0, (1 / 2), 0, 0, (1 / 2)], ![0, -1, 1, 0, 1, 0, 0, 1]], ![0, 1, 1, 0, -1, 0, 0, 1]⟩

theorem checked510 : certificate510.Checked := by decide +kernel

theorem dimension510 : Module.finrank ℚ (label 510) = 7 := certificate510.dimension checked510

theorem copy_rank510 : Module.finrank ℚ (LinearMap.range (-projector 510)) = 7 := certificate510.copy_rank checked510

def certificate511 : HyperplaneCertificate :=
  ⟨511, ![0, 3, 5, 6, 9, 11, 16], ![![1, (-1 / 2), (-1 / 2), 0, (1 / 2), 0, 0, (-1 / 2)], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, (-1 / 2), (-1 / 2), 0, (1 / 2), 0, 1, (-1 / 2)], ![0, (1 / 2), (1 / 2), 0, (1 / 2), 0, 0, (-1 / 2)], ![0, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, -1, 0, 0, 1]], ![0, -1, 1, 0, 1, 0, 0, 1]⟩

theorem checked511 : certificate511.Checked := by decide +kernel

theorem dimension511 : Module.finrank ℚ (label 511) = 7 := certificate511.dimension checked511

theorem copy_rank511 : Module.finrank ℚ (LinearMap.range (-projector 511)) = 7 := certificate511.copy_rank checked511

def certificate512 : HyperplaneCertificate :=
  ⟨512, ![0, 3, 4, 7, 11, 14, 30], ![![1, (-1 / 2), (-1 / 2), 0, 0, (-1 / 2), (-1 / 2), 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, -1, 0, 0, 1, 0, -1, 0], ![0, (-1 / 2), (1 / 2), 0, 0, (1 / 2), (-1 / 2), 1], ![0, 1, -1, 0, 0, -1, 1, 0], ![0, (1 / 2), (1 / 2), 0, 0, (-1 / 2), (3 / 2), 0], ![0, (1 / 2), (1 / 2), 0, 0, (3 / 2), (-1 / 2), 0]], ![0, -1, -1, 0, 0, 1, 1, 0]⟩

theorem checked512 : certificate512.Checked := by decide +kernel

theorem dimension512 : Module.finrank ℚ (label 512) = 7 := certificate512.dimension checked512

theorem copy_rank512 : Module.finrank ℚ (LinearMap.range (-projector 512)) = 7 := certificate512.copy_rank checked512

def certificate513 : HyperplaneCertificate :=
  ⟨513, ![0, 3, 4, 7, 8, 15, 31], ![![1, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, (-1 / 2), (-1 / 2), 0, 1, (1 / 2), (1 / 2), 0], ![0, (-1 / 2), (-1 / 2), 0, 0, (-1 / 2), (-1 / 2), 1], ![0, 1, 1, 0, 0, 1, 1, 0], ![0, (-1 / 2), (1 / 2), 0, 0, (-1 / 2), (-3 / 2), 0], ![0, (1 / 2), (-1 / 2), 0, 0, (-3 / 2), (-1 / 2), 0]], ![0, -1, 1, 0, 0, -1, 1, 0]⟩

theorem checked513 : certificate513.Checked := by decide +kernel

theorem dimension513 : Module.finrank ℚ (label 513) = 7 := certificate513.dimension checked513

theorem copy_rank513 : Module.finrank ℚ (LinearMap.range (-projector 513)) = 7 := certificate513.copy_rank checked513

def certificate514 : HyperplaneCertificate :=
  ⟨514, ![0, 1, 2, 3, 9, 15, 31], ![![1, 0, 0, 0, (-1 / 2), (1 / 2), (1 / 2), (-1 / 2)], ![0, 1, 0, 0, (-1 / 2), (1 / 2), (-1 / 2), (1 / 2)], ![0, 0, 1, 0, (-1 / 2), (-1 / 2), (1 / 2), (1 / 2)], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, (1 / 2), (1 / 2), (1 / 2), (-3 / 2)], ![0, 0, 0, 0, (1 / 2), (1 / 2), (-3 / 2), (1 / 2)], ![0, 0, 0, 0, (1 / 2), (-3 / 2), (1 / 2), (1 / 2)]], ![0, 0, 0, 0, 1, 1, 1, 1]⟩

theorem checked514 : certificate514.Checked := by decide +kernel

theorem dimension514 : Module.finrank ℚ (label 514) = 7 := certificate514.dimension checked514

theorem copy_rank514 : Module.finrank ℚ (LinearMap.range (-projector 514)) = 7 := certificate514.copy_rank checked514

def certificate515 : HyperplaneCertificate :=
  ⟨515, ![4, 5, 6, 7, 8, 14, 60], ![![0, 0, -1, -1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![(-1 / 2), (1 / 2), (-1 / 2), (-1 / 2), 0, 0, 1, 0], ![(1 / 2), (-1 / 2), (-1 / 2), (-1 / 2), 0, 0, 0, 1], ![-1, 1, 1, 1, 0, 0, 0, 0], ![1, -1, 1, 1, 0, 0, 0, 0], ![(1 / 2), (1 / 2), (-1 / 2), (-3 / 2), 0, 0, 0, 0]], ![1, 1, -1, 1, 0, 0, 0, 0]⟩

theorem checked515 : certificate515.Checked := by decide +kernel

theorem dimension515 : Module.finrank ℚ (label 515) = 7 := certificate515.dimension checked515

theorem copy_rank515 : Module.finrank ℚ (LinearMap.range (-projector 515)) = 7 := certificate515.copy_rank checked515

def certificate516 : HyperplaneCertificate :=
  ⟨516, ![1, 2, 5, 6, 9, 16, 60], ![![(-1 / 2), 1, 0, (1 / 2), (-1 / 2), 0, 0, (1 / 2)], ![-1, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![(-1 / 2), 0, 0, (-1 / 2), (1 / 2), 0, 1, (1 / 2)], ![(1 / 2), 0, 0, (1 / 2), (1 / 2), 0, 0, (-3 / 2)], ![1, 0, 0, 1, -1, 0, 0, -1], ![(1 / 2), 0, 0, (-3 / 2), (1 / 2), 0, 0, (1 / 2)]], ![1, 0, 0, 1, 1, 0, 0, 1]⟩

theorem checked516 : certificate516.Checked := by decide +kernel

theorem dimension516 : Module.finrank ℚ (label 516) = 7 := certificate516.dimension checked516

theorem copy_rank516 : Module.finrank ℚ (LinearMap.range (-projector 516)) = 7 := certificate516.copy_rank checked516

def certificate517 : HyperplaneCertificate :=
  ⟨517, ![0, 1, 4, 5, 8, 15, 60], ![![1, 0, (-1 / 2), (1 / 2), 0, 0, (1 / 2), (1 / 2)], ![0, 1, (-1 / 2), (1 / 2), 0, 0, (-1 / 2), (-1 / 2)], ![0, 0, (-1 / 2), (-1 / 2), 1, 0, (1 / 2), (-1 / 2)], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, (1 / 2), (1 / 2), 0, 0, (1 / 2), (3 / 2)], ![0, 0, (1 / 2), (1 / 2), 0, 0, (-3 / 2), (-1 / 2)], ![0, 0, (1 / 2), (-3 / 2), 0, 0, (1 / 2), (-1 / 2)]], ![0, 0, -1, -1, 0, 0, -1, 1]⟩

theorem checked517 : certificate517.Checked := by decide +kernel

theorem dimension517 : Module.finrank ℚ (label 517) = 7 := certificate517.dimension checked517

theorem copy_rank517 : Module.finrank ℚ (LinearMap.range (-projector 517)) = 7 := certificate517.copy_rank checked517

def certificate518 : HyperplaneCertificate :=
  ⟨518, ![0, 2, 4, 6, 8, 30, 59], ![![1, (-1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0, (1 / 2)], ![0, (-1 / 2), 1, (-1 / 2), 0, (1 / 2), 0, (-1 / 2)], ![0, (-1 / 2), 0, (1 / 2), 1, (-1 / 2), 0, (-1 / 2)], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, (1 / 2), 0, (-1 / 2), 0, (-1 / 2), 0, (3 / 2)], ![0, (1 / 2), 0, (-1 / 2), 0, (3 / 2), 0, (-1 / 2)], ![0, (1 / 2), 0, (3 / 2), 0, (-1 / 2), 0, (-1 / 2)]], ![0, -1, 0, 1, 0, 1, 0, 1]⟩

theorem checked518 : certificate518.Checked := by decide +kernel

theorem dimension518 : Module.finrank ℚ (label 518) = 7 := certificate518.dimension checked518

theorem copy_rank518 : Module.finrank ℚ (LinearMap.range (-projector 518)) = 7 := certificate518.copy_rank checked518

theorem copy_source_frames : Copy.lifecycles.map Copy.Lifecycle.sourceFrame = [510, 511, 512, 513, 514, 515, 516, 517, 518] := by decide +kernel

/-- Sum of ranks of the actual nine inverse-projector COPY operators. -/
theorem copy_rank_sum : (Copy.lifecycles.map (fun life => Module.finrank ℚ (LinearMap.range (-projector life.sourceFrame)))).sum = 63 := by
  have h := congrArg (fun fs : List ℕ => (fs.map (fun f => Module.finrank ℚ (LinearMap.range (-projector f)))).sum) copy_source_frames
  simpa [List.map_map, Function.comp_def, copy_rank510, copy_rank511, copy_rank512, copy_rank513, copy_rank514, copy_rank515, copy_rank516, copy_rank517, copy_rank518] using h

end IntegerMultBounds.Networks.Certificates.PR589.Geometry
