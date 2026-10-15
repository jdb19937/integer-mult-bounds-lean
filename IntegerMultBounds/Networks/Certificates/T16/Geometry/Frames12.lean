module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame384 : Frame := ⟨3, ![414#9,73#9,49#9], ![2#9,10#9,11#9]⟩
theorem frame384_dual : frame384.DualCheck := by decide
def checkedFrame384 : CertifiedFrame := ⟨frame384, frame384.independent frame384_dual⟩

def frame385 : Frame := ⟨4, ![386#9,73#9,45#9,28#9], ![2#9,12#9,13#9,9#9]⟩
theorem frame385_dual : frame385.DualCheck := by decide
def checkedFrame385 : CertifiedFrame := ⟨frame385, frame385.independent frame385_dual⟩

def frame386 : Frame := ⟨1, ![146#9], ![2#9]⟩
theorem frame386_dual : frame386.DualCheck := by decide
def checkedFrame386 : CertifiedFrame := ⟨frame386, frame386.independent frame386_dual⟩

def frame387 : Frame := ⟨1, ![289#9], ![1#9]⟩
theorem frame387_dual : frame387.DualCheck := by decide
def checkedFrame387 : CertifiedFrame := ⟨frame387, frame387.independent frame387_dual⟩

def frame388 : Frame := ⟨1, ![268#9], ![4#9]⟩
theorem frame388_dual : frame388.DualCheck := by decide
def checkedFrame388 : CertifiedFrame := ⟨frame388, frame388.independent frame388_dual⟩

def frame389 : Frame := ⟨1, ![191#9], ![1#9]⟩
theorem frame389_dual : frame389.DualCheck := by decide
def checkedFrame389 : CertifiedFrame := ⟨frame389, frame389.independent frame389_dual⟩

def frame390 : Frame := ⟨1, ![274#9], ![2#9]⟩
theorem frame390_dual : frame390.DualCheck := by decide
def checkedFrame390 : CertifiedFrame := ⟨frame390, frame390.independent frame390_dual⟩

def frame391 : Frame := ⟨1, ![161#9], ![1#9]⟩
theorem frame391_dual : frame391.DualCheck := by decide
def checkedFrame391 : CertifiedFrame := ⟨frame391, frame391.independent frame391_dual⟩

def frame392 : Frame := ⟨1, ![140#9], ![4#9]⟩
theorem frame392_dual : frame392.DualCheck := by decide
def checkedFrame392 : CertifiedFrame := ⟨frame392, frame392.independent frame392_dual⟩

def frame393 : Frame := ⟨1, ![319#9], ![1#9]⟩
theorem frame393_dual : frame393.DualCheck := by decide
def checkedFrame393 : CertifiedFrame := ⟨frame393, frame393.independent frame393_dual⟩

def frame394 : Frame := ⟨2, ![146#9,45#9], ![2#9,1#9]⟩
theorem frame394_dual : frame394.DualCheck := by decide
def checkedFrame394 : CertifiedFrame := ⟨frame394, frame394.independent frame394_dual⟩

def frame395 : Frame := ⟨2, ![146#9,51#9], ![3#9,1#9]⟩
theorem frame395_dual : frame395.DualCheck := by decide
def checkedFrame395 : CertifiedFrame := ⟨frame395, frame395.independent frame395_dual⟩

def frame396 : Frame := ⟨2, ![140#9,30#9], ![6#9,2#9]⟩
theorem frame396_dual : frame396.DualCheck := by decide
def checkedFrame396 : CertifiedFrame := ⟨frame396, frame396.independent frame396_dual⟩

def frame397 : Frame := ⟨2, ![268#9,45#9], ![5#9,1#9]⟩
theorem frame397_dual : frame397.DualCheck := by decide
def checkedFrame397 : CertifiedFrame := ⟨frame397, frame397.independent frame397_dual⟩

def frame398 : Frame := ⟨2, ![274#9,51#9], ![3#9,1#9]⟩
theorem frame398_dual : frame398.DualCheck := by decide
def checkedFrame398 : CertifiedFrame := ⟨frame398, frame398.independent frame398_dual⟩

def frame399 : Frame := ⟨2, ![289#9,30#9], ![1#9,2#9]⟩
theorem frame399_dual : frame399.DualCheck := by decide
def checkedFrame399 : CertifiedFrame := ⟨frame399, frame399.independent frame399_dual⟩

def frame400 : Frame := ⟨2, ![268#9,30#9], ![6#9,2#9]⟩
theorem frame400_dual : frame400.DualCheck := by decide
def checkedFrame400 : CertifiedFrame := ⟨frame400, frame400.independent frame400_dual⟩

def frame401 : Frame := ⟨2, ![268#9,51#9], ![4#9,1#9]⟩
theorem frame401_dual : frame401.DualCheck := by decide
def checkedFrame401 : CertifiedFrame := ⟨frame401, frame401.independent frame401_dual⟩

def frame402 : Frame := ⟨2, ![161#9,30#9], ![1#9,2#9]⟩
theorem frame402_dual : frame402.DualCheck := by decide
def checkedFrame402 : CertifiedFrame := ⟨frame402, frame402.independent frame402_dual⟩

def frame403 : Frame := ⟨2, ![140#9,51#9], ![4#9,1#9]⟩
theorem frame403_dual : frame403.DualCheck := by decide
def checkedFrame403 : CertifiedFrame := ⟨frame403, frame403.independent frame403_dual⟩

def frame404 : Frame := ⟨2, ![274#9,45#9], ![2#9,1#9]⟩
theorem frame404_dual : frame404.DualCheck := by decide
def checkedFrame404 : CertifiedFrame := ⟨frame404, frame404.independent frame404_dual⟩

def frame405 : Frame := ⟨2, ![140#9,45#9], ![5#9,1#9]⟩
theorem frame405_dual : frame405.DualCheck := by decide
def checkedFrame405 : CertifiedFrame := ⟨frame405, frame405.independent frame405_dual⟩

def frame406 : Frame := ⟨3, ![268#9,140#9,51#9], ![132#9,128#9,1#9]⟩
theorem frame406_dual : frame406.DualCheck := by decide
def checkedFrame406 : CertifiedFrame := ⟨frame406, frame406.independent frame406_dual⟩

def frame407 : Frame := ⟨3, ![274#9,146#9,51#9], ![131#9,128#9,1#9]⟩
theorem frame407_dual : frame407.DualCheck := by decide
def checkedFrame407 : CertifiedFrame := ⟨frame407, frame407.independent frame407_dual⟩

def frame408 : Frame := ⟨3, ![289#9,161#9,30#9], ![129#9,128#9,2#9]⟩
theorem frame408_dual : frame408.DualCheck := by decide
def checkedFrame408 : CertifiedFrame := ⟨frame408, frame408.independent frame408_dual⟩

def frame409 : Frame := ⟨3, ![268#9,140#9,30#9], ![134#9,128#9,2#9]⟩
theorem frame409_dual : frame409.DualCheck := by decide
def checkedFrame409 : CertifiedFrame := ⟨frame409, frame409.independent frame409_dual⟩

def frame410 : Frame := ⟨3, ![268#9,161#9,30#9], ![6#9,1#9,2#9]⟩
theorem frame410_dual : frame410.DualCheck := by decide
def checkedFrame410 : CertifiedFrame := ⟨frame410, frame410.independent frame410_dual⟩

def frame411 : Frame := ⟨3, ![289#9,140#9,30#9], ![1#9,6#9,2#9]⟩
theorem frame411_dual : frame411.DualCheck := by decide
def checkedFrame411 : CertifiedFrame := ⟨frame411, frame411.independent frame411_dual⟩

def frame412 : Frame := ⟨3, ![274#9,140#9,51#9], ![3#9,4#9,1#9]⟩
theorem frame412_dual : frame412.DualCheck := by decide
def checkedFrame412 : CertifiedFrame := ⟨frame412, frame412.independent frame412_dual⟩

def frame413 : Frame := ⟨3, ![268#9,146#9,51#9], ![4#9,3#9,1#9]⟩
theorem frame413_dual : frame413.DualCheck := by decide
def checkedFrame413 : CertifiedFrame := ⟨frame413, frame413.independent frame413_dual⟩

def frame414 : Frame := ⟨4, ![268#9,140#9,45#9,30#9], ![135#9,128#9,1#9,2#9]⟩
theorem frame414_dual : frame414.DualCheck := by decide
def checkedFrame414 : CertifiedFrame := ⟨frame414, frame414.independent frame414_dual⟩

def frame415 : Frame := ⟨8, ![256#9,128#9,64#9,34#9,16#9,10#9,4#9,1#9], ![256#9,128#9,64#9,10#9,16#9,8#9,4#9,1#9]⟩
theorem frame415_dual : frame415.DualCheck := by decide
def checkedFrame415 : CertifiedFrame := ⟨frame415, frame415.independent frame415_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
