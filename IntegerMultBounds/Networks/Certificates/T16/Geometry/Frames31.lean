module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame992 : Frame := ⟨8, ![257#9,128#9,64#9,33#9,17#9,9#9,5#9,3#9], ![63#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9]⟩
theorem frame992_dual : frame992.DualCheck := by decide
def checkedFrame992 : CertifiedFrame := ⟨frame992, frame992.independent frame992_dual⟩

def frame993 : Frame := ⟨6, ![259#9,192#9,33#9,18#9,8#9,4#9], ![18#9,64#9,19#9,16#9,8#9,4#9]⟩
theorem frame993_dual : frame993.DualCheck := by decide
def checkedFrame993 : CertifiedFrame := ⟨frame993, frame993.independent frame993_dual⟩

def frame994 : Frame := ⟨8, ![257#9,128#9,64#9,33#9,16#9,8#9,4#9,2#9], ![33#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9]⟩
theorem frame994_dual : frame994.DualCheck := by decide
def checkedFrame994 : CertifiedFrame := ⟨frame994, frame994.independent frame994_dual⟩

def frame995 : Frame := ⟨8, ![258#9,128#9,64#9,32#9,18#9,8#9,4#9,1#9], ![18#9,128#9,64#9,32#9,16#9,8#9,4#9,1#9]⟩
theorem frame995_dual : frame995.DualCheck := by decide
def checkedFrame995 : CertifiedFrame := ⟨frame995, frame995.independent frame995_dual⟩

def frame996 : Frame := ⟨6, ![263#9,134#9,70#9,33#9,18#9,12#9], ![33#9,109#9,64#9,32#9,14#9,8#9]⟩
theorem frame996_dual : frame996.DualCheck := by decide
def checkedFrame996 : CertifiedFrame := ⟨frame996, frame996.independent frame996_dual⟩

def frame997 : Frame := ⟨6, ![262#9,192#9,32#9,18#9,12#9,1#9], ![12#9,64#9,32#9,14#9,8#9,1#9]⟩
theorem frame997_dual : frame997.DualCheck := by decide
def checkedFrame997 : CertifiedFrame := ⟨frame997, frame997.independent frame997_dual⟩

def frame998 : Frame := ⟨8, ![256#9,128#9,64#9,33#9,17#9,8#9,4#9,3#9], ![256#9,128#9,64#9,19#9,16#9,8#9,4#9,2#9]⟩
theorem frame998_dual : frame998.DualCheck := by decide
def checkedFrame998 : CertifiedFrame := ⟨frame998, frame998.independent frame998_dual⟩

def frame999 : Frame := ⟨8, ![256#9,128#9,64#9,32#9,18#9,10#9,6#9,1#9], ![256#9,128#9,64#9,32#9,14#9,8#9,4#9,1#9]⟩
theorem frame999_dual : frame999.DualCheck := by decide
def checkedFrame999 : CertifiedFrame := ⟨frame999, frame999.independent frame999_dual⟩

def frame1000 : Frame := ⟨8, ![256#9,128#9,65#9,32#9,16#9,9#9,4#9,3#9], ![256#9,128#9,11#9,32#9,16#9,8#9,4#9,2#9]⟩
theorem frame1000_dual : frame1000.DualCheck := by decide
def checkedFrame1000 : CertifiedFrame := ⟨frame1000, frame1000.independent frame1000_dual⟩

def frame1001 : Frame := ⟨8, ![256#9,128#9,66#9,34#9,16#9,8#9,6#9,1#9], ![256#9,128#9,38#9,32#9,16#9,8#9,4#9,1#9]⟩
theorem frame1001_dual : frame1001.DualCheck := by decide
def checkedFrame1001 : CertifiedFrame := ⟨frame1001, frame1001.independent frame1001_dual⟩

def frame1002 : Frame := ⟨8, ![256#9,128#9,65#9,32#9,17#9,8#9,5#9,2#9], ![256#9,128#9,21#9,32#9,16#9,8#9,4#9,2#9]⟩
theorem frame1002_dual : frame1002.DualCheck := by decide
def checkedFrame1002 : CertifiedFrame := ⟨frame1002, frame1002.independent frame1002_dual⟩

def frame1003 : Frame := ⟨8, ![256#9,128#9,72#9,40#9,24#9,4#9,2#9,1#9], ![256#9,128#9,56#9,32#9,16#9,4#9,2#9,1#9]⟩
theorem frame1003_dual : frame1003.DualCheck := by decide
def checkedFrame1003 : CertifiedFrame := ⟨frame1003, frame1003.independent frame1003_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
