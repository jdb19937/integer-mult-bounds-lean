module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame128 : Frame := ⟨1, ![324#9], ![4#9]⟩
theorem frame128_dual : frame128.DualCheck := by decide
def checkedFrame128 : CertifiedFrame := ⟨frame128, frame128.independent frame128_dual⟩

def frame129 : Frame := ⟨1, ![145#9], ![1#9]⟩
theorem frame129_dual : frame129.DualCheck := by decide
def checkedFrame129 : CertifiedFrame := ⟨frame129, frame129.independent frame129_dual⟩

def frame130 : Frame := ⟨1, ![290#9], ![2#9]⟩
theorem frame130_dual : frame130.DualCheck := by decide
def checkedFrame130 : CertifiedFrame := ⟨frame130, frame130.independent frame130_dual⟩

def frame131 : Frame := ⟨1, ![273#9], ![1#9]⟩
theorem frame131_dual : frame131.DualCheck := by decide
def checkedFrame131 : CertifiedFrame := ⟨frame131, frame131.independent frame131_dual⟩

def frame132 : Frame := ⟨1, ![162#9], ![2#9]⟩
theorem frame132_dual : frame132.DualCheck := by decide
def checkedFrame132 : CertifiedFrame := ⟨frame132, frame132.independent frame132_dual⟩

def frame133 : Frame := ⟨2, ![324#9,51#9], ![4#9,1#9]⟩
theorem frame133_dual : frame133.DualCheck := by decide
def checkedFrame133 : CertifiedFrame := ⟨frame133, frame133.independent frame133_dual⟩

def frame134 : Frame := ⟨2, ![290#9,85#9], ![2#9,1#9]⟩
theorem frame134_dual : frame134.DualCheck := by decide
def checkedFrame134 : CertifiedFrame := ⟨frame134, frame134.independent frame134_dual⟩

def frame135 : Frame := ⟨2, ![273#9,102#9], ![1#9,2#9]⟩
theorem frame135_dual : frame135.DualCheck := by decide
def checkedFrame135 : CertifiedFrame := ⟨frame135, frame135.independent frame135_dual⟩

def frame136 : Frame := ⟨2, ![196#9,51#9], ![4#9,1#9]⟩
theorem frame136_dual : frame136.DualCheck := by decide
def checkedFrame136 : CertifiedFrame := ⟨frame136, frame136.independent frame136_dual⟩

def frame137 : Frame := ⟨2, ![145#9,85#9], ![5#9,4#9]⟩
theorem frame137_dual : frame137.DualCheck := by decide
def checkedFrame137 : CertifiedFrame := ⟨frame137, frame137.independent frame137_dual⟩

def frame138 : Frame := ⟨2, ![162#9,102#9], ![6#9,4#9]⟩
theorem frame138_dual : frame138.DualCheck := by decide
def checkedFrame138 : CertifiedFrame := ⟨frame138, frame138.independent frame138_dual⟩

def frame139 : Frame := ⟨2, ![145#9,102#9], ![1#9,2#9]⟩
theorem frame139_dual : frame139.DualCheck := by decide
def checkedFrame139 : CertifiedFrame := ⟨frame139, frame139.independent frame139_dual⟩

def frame140 : Frame := ⟨2, ![162#9,85#9], ![2#9,1#9]⟩
theorem frame140_dual : frame140.DualCheck := by decide
def checkedFrame140 : CertifiedFrame := ⟨frame140, frame140.independent frame140_dual⟩

def frame141 : Frame := ⟨2, ![290#9,102#9], ![6#9,4#9]⟩
theorem frame141_dual : frame141.DualCheck := by decide
def checkedFrame141 : CertifiedFrame := ⟨frame141, frame141.independent frame141_dual⟩

def frame142 : Frame := ⟨2, ![273#9,85#9], ![5#9,4#9]⟩
theorem frame142_dual : frame142.DualCheck := by decide
def checkedFrame142 : CertifiedFrame := ⟨frame142, frame142.independent frame142_dual⟩

def frame143 : Frame := ⟨2, ![145#9,51#9], ![3#9,2#9]⟩
theorem frame143_dual : frame143.DualCheck := by decide
def checkedFrame143 : CertifiedFrame := ⟨frame143, frame143.independent frame143_dual⟩

def frame144 : Frame := ⟨2, ![273#9,51#9], ![3#9,2#9]⟩
theorem frame144_dual : frame144.DualCheck := by decide
def checkedFrame144 : CertifiedFrame := ⟨frame144, frame144.independent frame144_dual⟩

def frame145 : Frame := ⟨3, ![273#9,162#9,85#9], ![5#9,2#9,4#9]⟩
theorem frame145_dual : frame145.DualCheck := by decide
def checkedFrame145 : CertifiedFrame := ⟨frame145, frame145.independent frame145_dual⟩

def frame146 : Frame := ⟨3, ![290#9,145#9,85#9], ![2#9,5#9,4#9]⟩
theorem frame146_dual : frame146.DualCheck := by decide
def checkedFrame146 : CertifiedFrame := ⟨frame146, frame146.independent frame146_dual⟩

def frame147 : Frame := ⟨3, ![290#9,162#9,102#9], ![134#9,128#9,4#9]⟩
theorem frame147_dual : frame147.DualCheck := by decide
def checkedFrame147 : CertifiedFrame := ⟨frame147, frame147.independent frame147_dual⟩

def frame148 : Frame := ⟨3, ![273#9,145#9,102#9], ![129#9,128#9,2#9]⟩
theorem frame148_dual : frame148.DualCheck := by decide
def checkedFrame148 : CertifiedFrame := ⟨frame148, frame148.independent frame148_dual⟩

def frame149 : Frame := ⟨3, ![290#9,145#9,102#9], ![6#9,1#9,4#9]⟩
theorem frame149_dual : frame149.DualCheck := by decide
def checkedFrame149 : CertifiedFrame := ⟨frame149, frame149.independent frame149_dual⟩

def frame150 : Frame := ⟨3, ![273#9,162#9,102#9], ![1#9,6#9,4#9]⟩
theorem frame150_dual : frame150.DualCheck := by decide
def checkedFrame150 : CertifiedFrame := ⟨frame150, frame150.independent frame150_dual⟩

def frame151 : Frame := ⟨3, ![273#9,145#9,85#9], ![133#9,128#9,4#9]⟩
theorem frame151_dual : frame151.DualCheck := by decide
def checkedFrame151 : CertifiedFrame := ⟨frame151, frame151.independent frame151_dual⟩

def frame152 : Frame := ⟨3, ![290#9,162#9,85#9], ![130#9,128#9,1#9]⟩
theorem frame152_dual : frame152.DualCheck := by decide
def checkedFrame152 : CertifiedFrame := ⟨frame152, frame152.independent frame152_dual⟩

def frame153 : Frame := ⟨4, ![273#9,145#9,85#9,51#9], ![135#9,128#9,4#9,2#9]⟩
theorem frame153_dual : frame153.DualCheck := by decide
def checkedFrame153 : CertifiedFrame := ⟨frame153, frame153.independent frame153_dual⟩

def frame154 : Frame := ⟨1, ![487#9], ![1#9]⟩
theorem frame154_dual : frame154.DualCheck := by decide
def checkedFrame154 : CertifiedFrame := ⟨frame154, frame154.independent frame154_dual⟩

def frame155 : Frame := ⟨1, ![84#9], ![4#9]⟩
theorem frame155_dual : frame155.DualCheck := by decide
def checkedFrame155 : CertifiedFrame := ⟨frame155, frame155.independent frame155_dual⟩

def frame156 : Frame := ⟨1, ![74#9], ![2#9]⟩
theorem frame156_dual : frame156.DualCheck := by decide
def checkedFrame156 : CertifiedFrame := ⟨frame156, frame156.independent frame156_dual⟩

def frame157 : Frame := ⟨1, ![505#9], ![1#9]⟩
theorem frame157_dual : frame157.DualCheck := by decide
def checkedFrame157 : CertifiedFrame := ⟨frame157, frame157.independent frame157_dual⟩

def frame158 : Frame := ⟨1, ![44#9], ![4#9]⟩
theorem frame158_dual : frame158.DualCheck := by decide
def checkedFrame158 : CertifiedFrame := ⟨frame158, frame158.independent frame158_dual⟩

def frame159 : Frame := ⟨1, ![415#9], ![1#9]⟩
theorem frame159_dual : frame159.DualCheck := by decide
def checkedFrame159 : CertifiedFrame := ⟨frame159, frame159.independent frame159_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
