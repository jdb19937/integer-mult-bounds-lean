module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame32 : Frame := ⟨3, ![486#9,21#9,11#9], ![10#9,9#9,8#9]⟩
theorem frame32_dual : frame32.DualCheck := by decide
def checkedFrame32 : CertifiedFrame := ⟨frame32, frame32.independent frame32_dual⟩

def frame33 : Frame := ⟨3, ![459#9,38#9,30#9], ![1#9,10#9,9#9]⟩
theorem frame33_dual : frame33.DualCheck := by decide
def checkedFrame33 : CertifiedFrame := ⟨frame33, frame33.independent frame33_dual⟩

def frame34 : Frame := ⟨3, ![448#9,21#9,11#9], ![64#9,3#9,2#9]⟩
theorem frame34_dual : frame34.DualCheck := by decide
def checkedFrame34 : CertifiedFrame := ⟨frame34, frame34.independent frame34_dual⟩

def frame35 : Frame := ⟨3, ![448#9,38#9,21#9], ![64#9,2#9,1#9]⟩
theorem frame35_dual : frame35.DualCheck := by decide
def checkedFrame35 : CertifiedFrame := ⟨frame35, frame35.independent frame35_dual⟩

def frame36 : Frame := ⟨3, ![469#9,51#9,11#9], ![3#9,10#9,8#9]⟩
theorem frame36_dual : frame36.DualCheck := by decide
def checkedFrame36 : CertifiedFrame := ⟨frame36, frame36.independent frame36_dual⟩

def frame37 : Frame := ⟨4, ![448#9,38#9,21#9,11#9], ![64#9,10#9,9#9,8#9]⟩
theorem frame37_dual : frame37.DualCheck := by decide
def checkedFrame37 : CertifiedFrame := ⟨frame37, frame37.independent frame37_dual⟩

def frame38 : Frame := ⟨1, ![208#9], ![16#9]⟩
theorem frame38_dual : frame38.DualCheck := by decide
def checkedFrame38 : CertifiedFrame := ⟨frame38, frame38.independent frame38_dual⟩

def frame39 : Frame := ⟨1, ![336#9], ![16#9]⟩
theorem frame39_dual : frame39.DualCheck := by decide
def checkedFrame39 : CertifiedFrame := ⟨frame39, frame39.independent frame39_dual⟩

def frame40 : Frame := ⟨1, ![381#9], ![1#9]⟩
theorem frame40_dual : frame40.DualCheck := by decide
def checkedFrame40 : CertifiedFrame := ⟨frame40, frame40.independent frame40_dual⟩

def frame41 : Frame := ⟨1, ![253#9], ![1#9]⟩
theorem frame41_dual : frame41.DualCheck := by decide
def checkedFrame41 : CertifiedFrame := ⟨frame41, frame41.independent frame41_dual⟩

def frame42 : Frame := ⟨1, ![296#9], ![8#9]⟩
theorem frame42_dual : frame42.DualCheck := by decide
def checkedFrame42 : CertifiedFrame := ⟨frame42, frame42.independent frame42_dual⟩

def frame43 : Frame := ⟨1, ![168#9], ![8#9]⟩
theorem frame43_dual : frame43.DualCheck := by decide
def checkedFrame43 : CertifiedFrame := ⟨frame43, frame43.independent frame43_dual⟩

def frame44 : Frame := ⟨1, ![133#9], ![1#9]⟩
theorem frame44_dual : frame44.DualCheck := by decide
def checkedFrame44 : CertifiedFrame := ⟨frame44, frame44.independent frame44_dual⟩

def frame45 : Frame := ⟨1, ![261#9], ![1#9]⟩
theorem frame45_dual : frame45.DualCheck := by decide
def checkedFrame45 : CertifiedFrame := ⟨frame45, frame45.independent frame45_dual⟩

def frame46 : Frame := ⟨2, ![208#9,45#9], ![16#9,1#9]⟩
theorem frame46_dual : frame46.DualCheck := by decide
def checkedFrame46 : CertifiedFrame := ⟨frame46, frame46.independent frame46_dual⟩

def frame47 : Frame := ⟨2, ![168#9,120#9], ![24#9,16#9]⟩
theorem frame47_dual : frame47.DualCheck := by decide
def checkedFrame47 : CertifiedFrame := ⟨frame47, frame47.independent frame47_dual⟩

def frame48 : Frame := ⟨2, ![133#9,85#9], ![17#9,16#9]⟩
theorem frame48_dual : frame48.DualCheck := by decide
def checkedFrame48 : CertifiedFrame := ⟨frame48, frame48.independent frame48_dual⟩

def frame49 : Frame := ⟨2, ![336#9,45#9], ![16#9,1#9]⟩
theorem frame49_dual : frame49.DualCheck := by decide
def checkedFrame49 : CertifiedFrame := ⟨frame49, frame49.independent frame49_dual⟩

def frame50 : Frame := ⟨2, ![296#9,120#9], ![24#9,16#9]⟩
theorem frame50_dual : frame50.DualCheck := by decide
def checkedFrame50 : CertifiedFrame := ⟨frame50, frame50.independent frame50_dual⟩

def frame51 : Frame := ⟨2, ![261#9,85#9], ![17#9,16#9]⟩
theorem frame51_dual : frame51.DualCheck := by decide
def checkedFrame51 : CertifiedFrame := ⟨frame51, frame51.independent frame51_dual⟩

def frame52 : Frame := ⟨2, ![296#9,85#9], ![8#9,1#9]⟩
theorem frame52_dual : frame52.DualCheck := by decide
def checkedFrame52 : CertifiedFrame := ⟨frame52, frame52.independent frame52_dual⟩

def frame53 : Frame := ⟨2, ![261#9,120#9], ![1#9,8#9]⟩
theorem frame53_dual : frame53.DualCheck := by decide
def checkedFrame53 : CertifiedFrame := ⟨frame53, frame53.independent frame53_dual⟩

def frame54 : Frame := ⟨2, ![168#9,85#9], ![8#9,1#9]⟩
theorem frame54_dual : frame54.DualCheck := by decide
def checkedFrame54 : CertifiedFrame := ⟨frame54, frame54.independent frame54_dual⟩

def frame55 : Frame := ⟨2, ![133#9,120#9], ![1#9,8#9]⟩
theorem frame55_dual : frame55.DualCheck := by decide
def checkedFrame55 : CertifiedFrame := ⟨frame55, frame55.independent frame55_dual⟩

def frame56 : Frame := ⟨2, ![261#9,45#9], ![9#9,8#9]⟩
theorem frame56_dual : frame56.DualCheck := by decide
def checkedFrame56 : CertifiedFrame := ⟨frame56, frame56.independent frame56_dual⟩

def frame57 : Frame := ⟨2, ![133#9,45#9], ![9#9,8#9]⟩
theorem frame57_dual : frame57.DualCheck := by decide
def checkedFrame57 : CertifiedFrame := ⟨frame57, frame57.independent frame57_dual⟩

def frame58 : Frame := ⟨3, ![261#9,133#9,120#9], ![129#9,128#9,8#9]⟩
theorem frame58_dual : frame58.DualCheck := by decide
def checkedFrame58 : CertifiedFrame := ⟨frame58, frame58.independent frame58_dual⟩

def frame59 : Frame := ⟨3, ![296#9,168#9,120#9], ![152#9,128#9,16#9]⟩
theorem frame59_dual : frame59.DualCheck := by decide
def checkedFrame59 : CertifiedFrame := ⟨frame59, frame59.independent frame59_dual⟩

def frame60 : Frame := ⟨3, ![261#9,168#9,85#9], ![17#9,8#9,16#9]⟩
theorem frame60_dual : frame60.DualCheck := by decide
def checkedFrame60 : CertifiedFrame := ⟨frame60, frame60.independent frame60_dual⟩

def frame61 : Frame := ⟨3, ![296#9,133#9,85#9], ![8#9,17#9,16#9]⟩
theorem frame61_dual : frame61.DualCheck := by decide
def checkedFrame61 : CertifiedFrame := ⟨frame61, frame61.independent frame61_dual⟩

def frame62 : Frame := ⟨3, ![296#9,168#9,85#9], ![136#9,128#9,1#9]⟩
theorem frame62_dual : frame62.DualCheck := by decide
def checkedFrame62 : CertifiedFrame := ⟨frame62, frame62.independent frame62_dual⟩

def frame63 : Frame := ⟨3, ![261#9,133#9,85#9], ![145#9,128#9,16#9]⟩
theorem frame63_dual : frame63.DualCheck := by decide
def checkedFrame63 : CertifiedFrame := ⟨frame63, frame63.independent frame63_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
