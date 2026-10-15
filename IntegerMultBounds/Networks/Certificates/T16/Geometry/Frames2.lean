module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame64 : Frame := ⟨3, ![296#9,133#9,120#9], ![24#9,1#9,16#9]⟩
theorem frame64_dual : frame64.DualCheck := by decide
def checkedFrame64 : CertifiedFrame := ⟨frame64, frame64.independent frame64_dual⟩

def frame65 : Frame := ⟨3, ![261#9,168#9,120#9], ![1#9,24#9,16#9]⟩
theorem frame65_dual : frame65.DualCheck := by decide
def checkedFrame65 : CertifiedFrame := ⟨frame65, frame65.independent frame65_dual⟩

def frame66 : Frame := ⟨4, ![261#9,133#9,85#9,45#9], ![153#9,128#9,16#9,8#9]⟩
theorem frame66_dual : frame66.DualCheck := by decide
def checkedFrame66 : CertifiedFrame := ⟨frame66, frame66.independent frame66_dual⟩

def frame67 : Frame := ⟨1, ![400#9], ![16#9]⟩
theorem frame67_dual : frame67.DualCheck := by decide
def checkedFrame67 : CertifiedFrame := ⟨frame67, frame67.independent frame67_dual⟩

def frame68 : Frame := ⟨1, ![35#9], ![1#9]⟩
theorem frame68_dual : frame68.DualCheck := by decide
def checkedFrame68 : CertifiedFrame := ⟨frame68, frame68.independent frame68_dual⟩

def frame69 : Frame := ⟨1, ![14#9], ![2#9]⟩
theorem frame69_dual : frame69.DualCheck := by decide
def checkedFrame69 : CertifiedFrame := ⟨frame69, frame69.independent frame69_dual⟩

def frame70 : Frame := ⟨1, ![445#9], ![1#9]⟩
theorem frame70_dual : frame70.DualCheck := by decide
def checkedFrame70 : CertifiedFrame := ⟨frame70, frame70.independent frame70_dual⟩

def frame71 : Frame := ⟨1, ![104#9], ![8#9]⟩
theorem frame71_dual : frame71.DualCheck := by decide
def checkedFrame71 : CertifiedFrame := ⟨frame71, frame71.independent frame71_dual⟩

def frame72 : Frame := ⟨1, ![475#9], ![1#9]⟩
theorem frame72_dual : frame72.DualCheck := by decide
def checkedFrame72 : CertifiedFrame := ⟨frame72, frame72.independent frame72_dual⟩

def frame73 : Frame := ⟨1, ![502#9], ![2#9]⟩
theorem frame73_dual : frame73.DualCheck := by decide
def checkedFrame73 : CertifiedFrame := ⟨frame73, frame73.independent frame73_dual⟩

def frame74 : Frame := ⟨1, ![69#9], ![1#9]⟩
theorem frame74_dual : frame74.DualCheck := by decide
def checkedFrame74 : CertifiedFrame := ⟨frame74, frame74.independent frame74_dual⟩

def frame75 : Frame := ⟨2, ![400#9,45#9], ![16#9,1#9]⟩
theorem frame75_dual : frame75.DualCheck := by decide
def checkedFrame75 : CertifiedFrame := ⟨frame75, frame75.independent frame75_dual⟩

def frame76 : Frame := ⟨2, ![400#9,75#9], ![16#9,1#9]⟩
theorem frame76_dual : frame76.DualCheck := by decide
def checkedFrame76 : CertifiedFrame := ⟨frame76, frame76.independent frame76_dual⟩

def frame77 : Frame := ⟨2, ![400#9,102#9], ![16#9,2#9]⟩
theorem frame77_dual : frame77.DualCheck := by decide
def checkedFrame77 : CertifiedFrame := ⟨frame77, frame77.independent frame77_dual⟩

def frame78 : Frame := ⟨2, ![35#9,14#9], ![1#9,3#9]⟩
theorem frame78_dual : frame78.DualCheck := by decide
def checkedFrame78 : CertifiedFrame := ⟨frame78, frame78.independent frame78_dual⟩

def frame79 : Frame := ⟨2, ![75#9,35#9], ![8#9,9#9]⟩
theorem frame79_dual : frame79.DualCheck := by decide
def checkedFrame79 : CertifiedFrame := ⟨frame79, frame79.independent frame79_dual⟩

def frame80 : Frame := ⟨2, ![69#9,35#9], ![3#9,2#9]⟩
theorem frame80_dual : frame80.DualCheck := by decide
def checkedFrame80 : CertifiedFrame := ⟨frame80, frame80.independent frame80_dual⟩

def frame81 : Frame := ⟨2, ![102#9,14#9], ![10#9,8#9]⟩
theorem frame81_dual : frame81.DualCheck := by decide
def checkedFrame81 : CertifiedFrame := ⟨frame81, frame81.independent frame81_dual⟩

def frame82 : Frame := ⟨2, ![69#9,14#9], ![1#9,2#9]⟩
theorem frame82_dual : frame82.DualCheck := by decide
def checkedFrame82 : CertifiedFrame := ⟨frame82, frame82.independent frame82_dual⟩

def frame83 : Frame := ⟨2, ![445#9,102#9], ![1#9,2#9]⟩
theorem frame83_dual : frame83.DualCheck := by decide
def checkedFrame83 : CertifiedFrame := ⟨frame83, frame83.independent frame83_dual⟩

def frame84 : Frame := ⟨2, ![445#9,75#9], ![3#9,2#9]⟩
theorem frame84_dual : frame84.DualCheck := by decide
def checkedFrame84 : CertifiedFrame := ⟨frame84, frame84.independent frame84_dual⟩

def frame85 : Frame := ⟨2, ![69#9,45#9], ![9#9,8#9]⟩
theorem frame85_dual : frame85.DualCheck := by decide
def checkedFrame85 : CertifiedFrame := ⟨frame85, frame85.independent frame85_dual⟩

def frame86 : Frame := ⟨2, ![475#9,45#9], ![2#9,3#9]⟩
theorem frame86_dual : frame86.DualCheck := by decide
def checkedFrame86 : CertifiedFrame := ⟨frame86, frame86.independent frame86_dual⟩

def frame87 : Frame := ⟨3, ![435#9,69#9,14#9], ![10#9,11#9,8#9]⟩
theorem frame87_dual : frame87.DualCheck := by decide
def checkedFrame87 : CertifiedFrame := ⟨frame87, frame87.independent frame87_dual⟩

def frame88 : Frame := ⟨3, ![400#9,75#9,35#9], ![16#9,8#9,9#9]⟩
theorem frame88_dual : frame88.DualCheck := by decide
def checkedFrame88 : CertifiedFrame := ⟨frame88, frame88.independent frame88_dual⟩

def frame89 : Frame := ⟨3, ![414#9,69#9,35#9], ![8#9,11#9,10#9]⟩
theorem frame89_dual : frame89.DualCheck := by decide
def checkedFrame89 : CertifiedFrame := ⟨frame89, frame89.independent frame89_dual⟩

def frame90 : Frame := ⟨3, ![400#9,102#9,14#9], ![16#9,10#9,8#9]⟩
theorem frame90_dual : frame90.DualCheck := by decide
def checkedFrame90 : CertifiedFrame := ⟨frame90, frame90.independent frame90_dual⟩

def frame91 : Frame := ⟨3, ![435#9,102#9,14#9], ![1#9,11#9,8#9]⟩
theorem frame91_dual : frame91.DualCheck := by decide
def checkedFrame91 : CertifiedFrame := ⟨frame91, frame91.independent frame91_dual⟩

def frame92 : Frame := ⟨3, ![400#9,69#9,35#9], ![16#9,3#9,2#9]⟩
theorem frame92_dual : frame92.DualCheck := by decide
def checkedFrame92 : CertifiedFrame := ⟨frame92, frame92.independent frame92_dual⟩

def frame93 : Frame := ⟨3, ![414#9,75#9,35#9], ![3#9,11#9,10#9]⟩
theorem frame93_dual : frame93.DualCheck := by decide
def checkedFrame93 : CertifiedFrame := ⟨frame93, frame93.independent frame93_dual⟩

def frame94 : Frame := ⟨3, ![400#9,69#9,14#9], ![16#9,1#9,2#9]⟩
theorem frame94_dual : frame94.DualCheck := by decide
def checkedFrame94 : CertifiedFrame := ⟨frame94, frame94.independent frame94_dual⟩

def frame95 : Frame := ⟨4, ![400#9,69#9,35#9,14#9], ![16#9,11#9,10#9,8#9]⟩
theorem frame95_dual : frame95.DualCheck := by decide
def checkedFrame95 : CertifiedFrame := ⟨frame95, frame95.independent frame95_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
