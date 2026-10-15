module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame448 : Frame := ⟨7, ![320#9,192#9,33#9,16#9,9#9,5#9,2#9], ![192#9,128#9,13#9,16#9,8#9,4#9,2#9]⟩
theorem frame448_dual : frame448.DualCheck := by decide
def checkedFrame448 : CertifiedFrame := ⟨frame448, frame448.independent frame448_dual⟩

def frame449 : Frame := ⟨7, ![272#9,128#9,80#9,33#9,9#9,5#9,2#9], ![80#9,128#9,64#9,13#9,8#9,4#9,2#9]⟩
theorem frame449_dual : frame449.DualCheck := by decide
def checkedFrame449 : CertifiedFrame := ⟨frame449, frame449.independent frame449_dual⟩

def frame450 : Frame := ⟨7, ![256#9,144#9,80#9,33#9,9#9,5#9,2#9], ![256#9,80#9,64#9,13#9,8#9,4#9,2#9]⟩
theorem frame450_dual : frame450.DualCheck := by decide
def checkedFrame450 : CertifiedFrame := ⟨frame450, frame450.independent frame450_dual⟩

def frame451 : Frame := ⟨7, ![256#9,128#9,64#9,33#9,16#9,11#9,7#9], ![256#9,128#9,64#9,3#9,16#9,6#9,4#9]⟩
theorem frame451_dual : frame451.DualCheck := by decide
def checkedFrame451 : CertifiedFrame := ⟨frame451, frame451.independent frame451_dual⟩

def frame452 : Frame := ⟨7, ![272#9,144#9,64#9,33#9,9#9,5#9,2#9], ![144#9,128#9,64#9,13#9,8#9,4#9,2#9]⟩
theorem frame452_dual : frame452.DualCheck := by decide
def checkedFrame452 : CertifiedFrame := ⟨frame452, frame452.independent frame452_dual⟩

def frame453 : Frame := ⟨3, ![469#9,38#9,11#9], ![9#9,10#9,8#9]⟩
theorem frame453_dual : frame453.DualCheck := by decide
def checkedFrame453 : CertifiedFrame := ⟨frame453, frame453.independent frame453_dual⟩

def frame454 : Frame := ⟨3, ![137#9,73#9,45#9], ![69#9,64#9,4#9]⟩
theorem frame454_dual : frame454.DualCheck := by decide
def checkedFrame454 : CertifiedFrame := ⟨frame454, frame454.independent frame454_dual⟩

def frame455 : Frame := ⟨3, ![265#9,222#9,45#9], ![7#9,2#9,6#9]⟩
theorem frame455_dual : frame455.DualCheck := by decide
def checkedFrame455 : CertifiedFrame := ⟨frame455, frame455.independent frame455_dual⟩

def frame456 : Frame := ⟨5, ![263#9,137#9,73#9,45#9,25#9], ![2#9,85#9,64#9,6#9,16#9]⟩
theorem frame456_dual : frame456.DualCheck := by decide
def checkedFrame456 : CertifiedFrame := ⟨frame456, frame456.independent frame456_dual⟩

def frame457 : Frame := ⟨4, ![469#9,36#9,9#9,2#9], ![9#9,13#9,8#9,2#9]⟩
theorem frame457_dual : frame457.DualCheck := by decide
def checkedFrame457 : CertifiedFrame := ⟨frame457, frame457.independent frame457_dual⟩

def frame458 : Frame := ⟨5, ![265#9,137#9,78#9,45#9,25#9], ![151#9,128#9,2#9,6#9,16#9]⟩
theorem frame458_dual : frame458.DualCheck := by decide
def checkedFrame458 : CertifiedFrame := ⟨frame458, frame458.independent frame458_dual⟩

def frame459 : Frame := ⟨6, ![258#9,130#9,69#9,38#9,18#9,11#9], ![151#9,128#9,9#9,13#9,16#9,8#9]⟩
theorem frame459_dual : frame459.DualCheck := by decide
def checkedFrame459 : CertifiedFrame := ⟨frame459, frame459.independent frame459_dual⟩

def frame460 : Frame := ⟨6, ![389#9,64#9,36#9,16#9,9#9,2#9], ![9#9,64#9,13#9,16#9,8#9,2#9]⟩
theorem frame460_dual : frame460.DualCheck := by decide
def checkedFrame460 : CertifiedFrame := ⟨frame460, frame460.independent frame460_dual⟩

def frame461 : Frame := ⟨6, ![263#9,135#9,71#9,35#9,23#9,14#9], ![215#9,128#9,64#9,6#9,16#9,3#9]⟩
theorem frame461_dual : frame461.DualCheck := by decide
def checkedFrame461 : CertifiedFrame := ⟨frame461, frame461.independent frame461_dual⟩

def frame462 : Frame := ⟨7, ![258#9,130#9,66#9,33#9,18#9,11#9,7#9], ![222#9,128#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame462_dual : frame462.DualCheck := by decide
def checkedFrame462 : CertifiedFrame := ⟨frame462, frame462.independent frame462_dual⟩

def frame463 : Frame := ⟨7, ![256#9,133#9,64#9,36#9,16#9,9#9,2#9], ![256#9,9#9,64#9,13#9,16#9,8#9,2#9]⟩
theorem frame463_dual : frame463.DualCheck := by decide
def checkedFrame463 : CertifiedFrame := ⟨frame463, frame463.independent frame463_dual⟩

def frame464 : Frame := ⟨7, ![261#9,128#9,64#9,36#9,16#9,9#9,2#9], ![9#9,128#9,64#9,13#9,16#9,8#9,2#9]⟩
theorem frame464_dual : frame464.DualCheck := by decide
def checkedFrame464 : CertifiedFrame := ⟨frame464, frame464.independent frame464_dual⟩

def frame465 : Frame := ⟨7, ![258#9,130#9,66#9,35#9,18#9,11#9,5#9], ![215#9,128#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame465_dual : frame465.DualCheck := by decide
def checkedFrame465 : CertifiedFrame := ⟨frame465, frame465.independent frame465_dual⟩

def frame466 : Frame := ⟨7, ![256#9,128#9,69#9,36#9,16#9,9#9,2#9], ![256#9,128#9,9#9,13#9,16#9,8#9,2#9]⟩
theorem frame466_dual : frame466.DualCheck := by decide
def checkedFrame466 : CertifiedFrame := ⟨frame466, frame466.independent frame466_dual⟩

def frame467 : Frame := ⟨3, ![261#9,208#9,45#9], ![9#9,16#9,8#9]⟩
theorem frame467_dual : frame467.DualCheck := by decide
def checkedFrame467 : CertifiedFrame := ⟨frame467, frame467.independent frame467_dual⟩

def frame468 : Frame := ⟨3, ![146#9,80#9,45#9], ![2#9,18#9,1#9]⟩
theorem frame468_dual : frame468.DualCheck := by decide
def checkedFrame468 : CertifiedFrame := ⟨frame468, frame468.independent frame468_dual⟩

def frame469 : Frame := ⟨3, ![265#9,40#9,5#9], ![5#9,13#9,4#9]⟩
theorem frame469_dual : frame469.DualCheck := by decide
def checkedFrame469 : CertifiedFrame := ⟨frame469, frame469.independent frame469_dual⟩

def frame470 : Frame := ⟨4, ![261#9,146#9,80#9,45#9], ![9#9,2#9,18#9,8#9]⟩
theorem frame470_dual : frame470.DualCheck := by decide
def checkedFrame470 : CertifiedFrame := ⟨frame470, frame470.independent frame470_dual⟩

def frame471 : Frame := ⟨4, ![261#9,208#9,36#9,9#9], ![9#9,16#9,13#9,8#9]⟩
theorem frame471_dual : frame471.DualCheck := by decide
def checkedFrame471 : CertifiedFrame := ⟨frame471, frame471.independent frame471_dual⟩

def frame472 : Frame := ⟨5, ![265#9,144#9,82#9,40#9,5#9], ![5#9,18#9,2#9,13#9,4#9]⟩
theorem frame472_dual : frame472.DualCheck := by decide
def checkedFrame472 : CertifiedFrame := ⟨frame472, frame472.independent frame472_dual⟩

def frame473 : Frame := ⟨6, ![265#9,130#9,64#9,40#9,18#9,5#9], ![5#9,18#9,64#9,13#9,16#9,4#9]⟩
theorem frame473_dual : frame473.DualCheck := by decide
def checkedFrame473 : CertifiedFrame := ⟨frame473, frame473.independent frame473_dual⟩

def frame474 : Frame := ⟨6, ![261#9,130#9,66#9,36#9,16#9,9#9], ![9#9,66#9,64#9,13#9,16#9,8#9]⟩
theorem frame474_dual : frame474.DualCheck := by decide
def checkedFrame474 : CertifiedFrame := ⟨frame474, frame474.independent frame474_dual⟩

def frame475 : Frame := ⟨6, ![261#9,144#9,80#9,33#9,12#9,2#9], ![12#9,80#9,64#9,13#9,8#9,2#9]⟩
theorem frame475_dual : frame475.DualCheck := by decide
def checkedFrame475 : CertifiedFrame := ⟨frame475, frame475.independent frame475_dual⟩

def frame476 : Frame := ⟨7, ![265#9,128#9,64#9,40#9,16#9,5#9,2#9], ![5#9,128#9,64#9,13#9,16#9,4#9,2#9]⟩
theorem frame476_dual : frame476.DualCheck := by decide
def checkedFrame476 : CertifiedFrame := ⟨frame476, frame476.independent frame476_dual⟩

def frame477 : Frame := ⟨7, ![256#9,130#9,66#9,33#9,16#9,9#9,5#9], ![256#9,66#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame477_dual : frame477.DualCheck := by decide
def checkedFrame477 : CertifiedFrame := ⟨frame477, frame477.independent frame477_dual⟩

def frame478 : Frame := ⟨7, ![261#9,128#9,64#9,33#9,16#9,12#9,2#9], ![12#9,128#9,64#9,13#9,16#9,8#9,2#9]⟩
theorem frame478_dual : frame478.DualCheck := by decide
def checkedFrame478 : CertifiedFrame := ⟨frame478, frame478.independent frame478_dual⟩

def frame479 : Frame := ⟨7, ![256#9,130#9,64#9,33#9,18#9,9#9,5#9], ![256#9,18#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame479_dual : frame479.DualCheck := by decide
def checkedFrame479 : CertifiedFrame := ⟨frame479, frame479.independent frame479_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
