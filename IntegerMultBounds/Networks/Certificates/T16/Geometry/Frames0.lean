module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame0 : Frame := ⟨0, ![], ![]⟩
theorem frame0_dual : frame0.DualCheck := by decide
def checkedFrame0 : CertifiedFrame := ⟨frame0, frame0.independent frame0_dual⟩

def frame1 : Frame := ⟨9, ![256#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9,1#9], ![256#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9,1#9]⟩
theorem frame1_dual : frame1.DualCheck := by decide
def checkedFrame1 : CertifiedFrame := ⟨frame1, frame1.independent frame1_dual⟩

def frame2 : Frame := ⟨1, ![30#9], ![2#9]⟩
theorem frame2_dual : frame2.DualCheck := by decide
def checkedFrame2 : CertifiedFrame := ⟨frame2, frame2.independent frame2_dual⟩

def frame3 : Frame := ⟨1, ![51#9], ![1#9]⟩
theorem frame3_dual : frame3.DualCheck := by decide
def checkedFrame3 : CertifiedFrame := ⟨frame3, frame3.independent frame3_dual⟩

def frame4 : Frame := ⟨1, ![459#9], ![1#9]⟩
theorem frame4_dual : frame4.DualCheck := by decide
def checkedFrame4 : CertifiedFrame := ⟨frame4, frame4.independent frame4_dual⟩

def frame5 : Frame := ⟨1, ![75#9], ![1#9]⟩
theorem frame5_dual : frame5.DualCheck := by decide
def checkedFrame5 : CertifiedFrame := ⟨frame5, frame5.independent frame5_dual⟩

def frame6 : Frame := ⟨1, ![102#9], ![2#9]⟩
theorem frame6_dual : frame6.DualCheck := by decide
def checkedFrame6 : CertifiedFrame := ⟨frame6, frame6.independent frame6_dual⟩

def frame7 : Frame := ⟨1, ![120#9], ![8#9]⟩
theorem frame7_dual : frame7.DualCheck := by decide
def checkedFrame7 : CertifiedFrame := ⟨frame7, frame7.independent frame7_dual⟩

def frame8 : Frame := ⟨1, ![85#9], ![1#9]⟩
theorem frame8_dual : frame8.DualCheck := by decide
def checkedFrame8 : CertifiedFrame := ⟨frame8, frame8.independent frame8_dual⟩

def frame9 : Frame := ⟨1, ![11#9], ![1#9]⟩
theorem frame9_dual : frame9.DualCheck := by decide
def checkedFrame9 : CertifiedFrame := ⟨frame9, frame9.independent frame9_dual⟩

def frame10 : Frame := ⟨1, ![448#9], ![64#9]⟩
theorem frame10_dual : frame10.DualCheck := by decide
def checkedFrame10 : CertifiedFrame := ⟨frame10, frame10.independent frame10_dual⟩

def frame11 : Frame := ⟨1, ![493#9], ![1#9]⟩
theorem frame11_dual : frame11.DualCheck := by decide
def checkedFrame11 : CertifiedFrame := ⟨frame11, frame11.independent frame11_dual⟩

def frame12 : Frame := ⟨1, ![38#9], ![2#9]⟩
theorem frame12_dual : frame12.DualCheck := by decide
def checkedFrame12 : CertifiedFrame := ⟨frame12, frame12.independent frame12_dual⟩

def frame13 : Frame := ⟨1, ![499#9], ![1#9]⟩
theorem frame13_dual : frame13.DualCheck := by decide
def checkedFrame13 : CertifiedFrame := ⟨frame13, frame13.independent frame13_dual⟩

def frame14 : Frame := ⟨1, ![56#9], ![8#9]⟩
theorem frame14_dual : frame14.DualCheck := by decide
def checkedFrame14 : CertifiedFrame := ⟨frame14, frame14.independent frame14_dual⟩

def frame15 : Frame := ⟨1, ![21#9], ![1#9]⟩
theorem frame15_dual : frame15.DualCheck := by decide
def checkedFrame15 : CertifiedFrame := ⟨frame15, frame15.independent frame15_dual⟩

def frame16 : Frame := ⟨1, ![478#9], ![2#9]⟩
theorem frame16_dual : frame16.DualCheck := by decide
def checkedFrame16 : CertifiedFrame := ⟨frame16, frame16.independent frame16_dual⟩

def frame17 : Frame := ⟨2, ![38#9,11#9], ![3#9,1#9]⟩
theorem frame17_dual : frame17.DualCheck := by decide
def checkedFrame17 : CertifiedFrame := ⟨frame17, frame17.independent frame17_dual⟩

def frame18 : Frame := ⟨2, ![51#9,11#9], ![9#9,8#9]⟩
theorem frame18_dual : frame18.DualCheck := by decide
def checkedFrame18 : CertifiedFrame := ⟨frame18, frame18.independent frame18_dual⟩

def frame19 : Frame := ⟨2, ![21#9,11#9], ![3#9,2#9]⟩
theorem frame19_dual : frame19.DualCheck := by decide
def checkedFrame19 : CertifiedFrame := ⟨frame19, frame19.independent frame19_dual⟩

def frame20 : Frame := ⟨2, ![448#9,45#9], ![64#9,1#9]⟩
theorem frame20_dual : frame20.DualCheck := by decide
def checkedFrame20 : CertifiedFrame := ⟨frame20, frame20.independent frame20_dual⟩

def frame21 : Frame := ⟨2, ![448#9,51#9], ![64#9,1#9]⟩
theorem frame21_dual : frame21.DualCheck := by decide
def checkedFrame21 : CertifiedFrame := ⟨frame21, frame21.independent frame21_dual⟩

def frame22 : Frame := ⟨2, ![448#9,30#9], ![64#9,2#9]⟩
theorem frame22_dual : frame22.DualCheck := by decide
def checkedFrame22 : CertifiedFrame := ⟨frame22, frame22.independent frame22_dual⟩

def frame23 : Frame := ⟨2, ![493#9,30#9], ![1#9,2#9]⟩
theorem frame23_dual : frame23.DualCheck := by decide
def checkedFrame23 : CertifiedFrame := ⟨frame23, frame23.independent frame23_dual⟩

def frame24 : Frame := ⟨2, ![478#9,51#9], ![3#9,1#9]⟩
theorem frame24_dual : frame24.DualCheck := by decide
def checkedFrame24 : CertifiedFrame := ⟨frame24, frame24.independent frame24_dual⟩

def frame25 : Frame := ⟨2, ![38#9,30#9], ![10#9,8#9]⟩
theorem frame25_dual : frame25.DualCheck := by decide
def checkedFrame25 : CertifiedFrame := ⟨frame25, frame25.independent frame25_dual⟩

def frame26 : Frame := ⟨2, ![38#9,21#9], ![2#9,1#9]⟩
theorem frame26_dual : frame26.DualCheck := by decide
def checkedFrame26 : CertifiedFrame := ⟨frame26, frame26.independent frame26_dual⟩

def frame27 : Frame := ⟨2, ![478#9,45#9], ![2#9,1#9]⟩
theorem frame27_dual : frame27.DualCheck := by decide
def checkedFrame27 : CertifiedFrame := ⟨frame27, frame27.independent frame27_dual⟩

def frame28 : Frame := ⟨2, ![45#9,21#9], ![8#9,9#9]⟩
theorem frame28_dual : frame28.DualCheck := by decide
def checkedFrame28 : CertifiedFrame := ⟨frame28, frame28.independent frame28_dual⟩

def frame29 : Frame := ⟨3, ![459#9,38#9,21#9], ![8#9,10#9,9#9]⟩
theorem frame29_dual : frame29.DualCheck := by decide
def checkedFrame29 : CertifiedFrame := ⟨frame29, frame29.independent frame29_dual⟩

def frame30 : Frame := ⟨3, ![448#9,51#9,11#9], ![64#9,9#9,8#9]⟩
theorem frame30_dual : frame30.DualCheck := by decide
def checkedFrame30 : CertifiedFrame := ⟨frame30, frame30.independent frame30_dual⟩

def frame31 : Frame := ⟨3, ![448#9,38#9,30#9], ![64#9,10#9,8#9]⟩
theorem frame31_dual : frame31.DualCheck := by decide
def checkedFrame31 : CertifiedFrame := ⟨frame31, frame31.independent frame31_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
