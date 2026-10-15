module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame512 : Frame := ⟨6, ![256#9,128#9,89#9,40#9,5#9,2#9], ![256#9,128#9,5#9,13#9,4#9,2#9]⟩
theorem frame512_dual : frame512.DualCheck := by decide
def checkedFrame512 : CertifiedFrame := ⟨frame512, frame512.independent frame512_dual⟩

def frame513 : Frame := ⟨7, ![256#9,128#9,64#9,40#9,25#9,5#9,2#9], ![256#9,128#9,64#9,13#9,5#9,4#9,2#9]⟩
theorem frame513_dual : frame513.DualCheck := by decide
def checkedFrame513 : CertifiedFrame := ⟨frame513, frame513.independent frame513_dual⟩

def frame514 : Frame := ⟨7, ![256#9,137#9,64#9,40#9,16#9,5#9,2#9], ![256#9,5#9,64#9,13#9,16#9,4#9,2#9]⟩
theorem frame514_dual : frame514.DualCheck := by decide
def checkedFrame514 : CertifiedFrame := ⟨frame514, frame514.independent frame514_dual⟩

def frame515 : Frame := ⟨3, ![448#9,45#9,21#9], ![64#9,8#9,9#9]⟩
theorem frame515_dual : frame515.DualCheck := by decide
def checkedFrame515 : CertifiedFrame := ⟨frame515, frame515.independent frame515_dual⟩

def frame516 : Frame := ⟨3, ![194#9,45#9,28#9], ![2#9,1#9,5#9]⟩
theorem frame516_dual : frame516.DualCheck := by decide
def checkedFrame516 : CertifiedFrame := ⟨frame516, frame516.independent frame516_dual⟩

def frame517 : Frame := ⟨3, ![322#9,192#9,45#9], ![2#9,66#9,1#9]⟩
theorem frame517_dual : frame517.DualCheck := by decide
def checkedFrame517 : CertifiedFrame := ⟨frame517, frame517.independent frame517_dual⟩

def frame518 : Frame := ⟨4, ![258#9,194#9,45#9,28#9], ![66#9,64#9,1#9,5#9]⟩
theorem frame518_dual : frame518.DualCheck := by decide
def checkedFrame518 : CertifiedFrame := ⟨frame518, frame518.independent frame518_dual⟩

def frame519 : Frame := ⟨4, ![386#9,66#9,45#9,21#9], ![66#9,64#9,8#9,9#9]⟩
theorem frame519_dual : frame519.DualCheck := by decide
def checkedFrame519 : CertifiedFrame := ⟨frame519, frame519.independent frame519_dual⟩

def frame520 : Frame := ⟨4, ![320#9,192#9,45#9,2#9], ![192#9,128#9,1#9,2#9]⟩
theorem frame520_dual : frame520.DualCheck := by decide
def checkedFrame520 : CertifiedFrame := ⟨frame520, frame520.independent frame520_dual⟩

def frame521 : Frame := ⟨6, ![320#9,192#9,33#9,21#9,12#9,2#9], ![192#9,128#9,13#9,12#9,8#9,2#9]⟩
theorem frame521_dual : frame521.DualCheck := by decide
def checkedFrame521 : CertifiedFrame := ⟨frame521, frame521.independent frame521_dual⟩

def frame522 : Frame := ⟨6, ![386#9,66#9,33#9,16#9,9#9,5#9], ![66#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame522_dual : frame522.DualCheck := by decide
def checkedFrame522 : CertifiedFrame := ⟨frame522, frame522.independent frame522_dual⟩

def frame523 : Frame := ⟨6, ![258#9,130#9,64#9,40#9,25#9,5#9], ![130#9,128#9,64#9,13#9,5#9,4#9]⟩
theorem frame523_dual : frame523.DualCheck := by decide
def checkedFrame523 : CertifiedFrame := ⟨frame523, frame523.independent frame523_dual⟩

def frame524 : Frame := ⟨7, ![258#9,128#9,66#9,33#9,16#9,9#9,5#9], ![66#9,128#9,64#9,13#9,16#9,8#9,4#9]⟩
theorem frame524_dual : frame524.DualCheck := by decide
def checkedFrame524 : CertifiedFrame := ⟨frame524, frame524.independent frame524_dual⟩

def frame525 : Frame := ⟨3, ![336#9,133#9,45#9], ![16#9,9#9,8#9]⟩
theorem frame525_dual : frame525.DualCheck := by decide
def checkedFrame525 : CertifiedFrame := ⟨frame525, frame525.independent frame525_dual⟩

def frame526 : Frame := ⟨3, ![137#9,40#9,5#9], ![5#9,13#9,4#9]⟩
theorem frame526_dual : frame526.DualCheck := by decide
def checkedFrame526 : CertifiedFrame := ⟨frame526, frame526.independent frame526_dual⟩

def frame527 : Frame := ⟨3, ![274#9,80#9,45#9], ![2#9,18#9,1#9]⟩
theorem frame527_dual : frame527.DualCheck := by decide
def checkedFrame527 : CertifiedFrame := ⟨frame527, frame527.independent frame527_dual⟩

def frame528 : Frame := ⟨4, ![336#9,137#9,40#9,5#9], ![16#9,5#9,13#9,4#9]⟩
theorem frame528_dual : frame528.DualCheck := by decide
def checkedFrame528 : CertifiedFrame := ⟨frame528, frame528.independent frame528_dual⟩

def frame529 : Frame := ⟨4, ![274#9,133#9,66#9,45#9], ![16#9,9#9,18#9,8#9]⟩
theorem frame529_dual : frame529.DualCheck := by decide
def checkedFrame529 : CertifiedFrame := ⟨frame529, frame529.independent frame529_dual⟩

def frame530 : Frame := ⟨4, ![274#9,137#9,80#9,45#9], ![2#9,5#9,18#9,4#9]⟩
theorem frame530_dual : frame530.DualCheck := by decide
def checkedFrame530 : CertifiedFrame := ⟨frame530, frame530.independent frame530_dual⟩

def frame531 : Frame := ⟨6, ![272#9,133#9,80#9,33#9,12#9,2#9], ![80#9,12#9,64#9,13#9,8#9,2#9]⟩
theorem frame531_dual : frame531.DualCheck := by decide
def checkedFrame531 : CertifiedFrame := ⟨frame531, frame531.independent frame531_dual⟩

def frame532 : Frame := ⟨6, ![258#9,133#9,66#9,36#9,16#9,9#9], ![66#9,9#9,64#9,13#9,16#9,8#9]⟩
theorem frame532_dual : frame532.DualCheck := by decide
def checkedFrame532 : CertifiedFrame := ⟨frame532, frame532.independent frame532_dual⟩

def frame533 : Frame := ⟨6, ![258#9,137#9,64#9,40#9,18#9,5#9], ![18#9,5#9,64#9,13#9,16#9,4#9]⟩
theorem frame533_dual : frame533.DualCheck := by decide
def checkedFrame533 : CertifiedFrame := ⟨frame533, frame533.independent frame533_dual⟩

def frame534 : Frame := ⟨3, ![414#9,81#9,51#9], ![4#9,7#9,6#9]⟩
theorem frame534_dual : frame534.DualCheck := by decide
def checkedFrame534 : CertifiedFrame := ⟨frame534, frame534.independent frame534_dual⟩

def frame535 : Frame := ⟨3, ![388#9,41#9,26#9], ![4#9,1#9,2#9]⟩
theorem frame535_dual : frame535.DualCheck := by decide
def checkedFrame535 : CertifiedFrame := ⟨frame535, frame535.independent frame535_dual⟩

def frame536 : Frame := ⟨3, ![388#9,81#9,51#9], ![4#9,3#9,2#9]⟩
theorem frame536_dual : frame536.DualCheck := by decide
def checkedFrame536 : CertifiedFrame := ⟨frame536, frame536.independent frame536_dual⟩

def frame537 : Frame := ⟨3, ![463#9,41#9,26#9], ![4#9,5#9,6#9]⟩
theorem frame537_dual : frame537.DualCheck := by decide
def checkedFrame537 : CertifiedFrame := ⟨frame537, frame537.independent frame537_dual⟩

def frame538 : Frame := ⟨6, ![387#9,64#9,34#9,17#9,8#9,4#9], ![17#9,64#9,19#9,16#9,8#9,4#9]⟩
theorem frame538_dual : frame538.DualCheck := by decide
def checkedFrame538 : CertifiedFrame := ⟨frame538, frame538.independent frame538_dual⟩

def frame539 : Frame := ⟨6, ![388#9,68#9,33#9,17#9,8#9,3#9], ![68#9,64#9,19#9,16#9,8#9,2#9]⟩
theorem frame539_dual : frame539.DualCheck := by decide
def checkedFrame539 : CertifiedFrame := ⟨frame539, frame539.independent frame539_dual⟩

def frame540 : Frame := ⟨3, ![273#9,145#9,51#9], ![131#9,128#9,2#9]⟩
theorem frame540_dual : frame540.DualCheck := by decide
def checkedFrame540 : CertifiedFrame := ⟨frame540, frame540.independent frame540_dual⟩

def frame541 : Frame := ⟨3, ![324#9,196#9,51#9], ![132#9,128#9,1#9]⟩
theorem frame541_dual : frame541.DualCheck := by decide
def checkedFrame541 : CertifiedFrame := ⟨frame541, frame541.independent frame541_dual⟩

def frame542 : Frame := ⟨3, ![273#9,196#9,51#9], ![3#9,4#9,2#9]⟩
theorem frame542_dual : frame542.DualCheck := by decide
def checkedFrame542 : CertifiedFrame := ⟨frame542, frame542.independent frame542_dual⟩

def frame543 : Frame := ⟨3, ![324#9,145#9,51#9], ![4#9,3#9,2#9]⟩
theorem frame543_dual : frame543.DualCheck := by decide
def checkedFrame543 : CertifiedFrame := ⟨frame543, frame543.independent frame543_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
