module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix128 : MatrixWitness := ⟨![324#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,260#9,8#9,16#9,32#9,320#9,128#9]⟩
theorem matrix128_dual : matrix128.DualCheck := by decide
noncomputable def extension128 : FrameExtension frame128 :=
  matrix128.extension matrix128_dual frame128 (by decide) (by decide)

def matrix129 : MatrixWitness := ⟨![145#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,2#9,4#9,8#9,144#9,32#9,64#9,256#9]⟩
theorem matrix129_dual : matrix129.DualCheck := by decide
noncomputable def extension129 : FrameExtension frame129 :=
  matrix129.extension matrix129_dual frame129 (by decide) (by decide)

def matrix130 : MatrixWitness := ⟨![290#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,4#9,8#9,16#9,288#9,64#9,128#9]⟩
theorem matrix130_dual : matrix130.DualCheck := by decide
noncomputable def extension130 : FrameExtension frame130 :=
  matrix130.extension matrix130_dual frame130 (by decide) (by decide)

def matrix131 : MatrixWitness := ⟨![273#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,4#9,8#9,272#9,32#9,64#9,128#9]⟩
theorem matrix131_dual : matrix131.DualCheck := by decide
noncomputable def extension131 : FrameExtension frame131 :=
  matrix131.extension matrix131_dual frame131 (by decide) (by decide)

def matrix132 : MatrixWitness := ⟨![162#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,130#9,4#9,8#9,16#9,160#9,64#9,256#9]⟩
theorem matrix132_dual : matrix132.DualCheck := by decide
noncomputable def extension132 : FrameExtension frame132 :=
  matrix132.extension matrix132_dual frame132 (by decide) (by decide)

def matrix133 : MatrixWitness := ⟨![324#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,34#9,260#9,8#9,48#9,320#9,128#9]⟩
theorem matrix133_dual : matrix133.DualCheck := by decide
noncomputable def extension133 : FrameExtension frame133 :=
  matrix133.extension matrix133_dual frame133 (by decide) (by decide)

def matrix134 : MatrixWitness := ⟨![290#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,65#9,258#9,68#9,8#9,80#9,288#9,128#9]⟩
theorem matrix134_dual : matrix134.DualCheck := by decide
noncomputable def extension134 : FrameExtension frame134 :=
  matrix134.extension matrix134_dual frame134 (by decide) (by decide)

def matrix135 : MatrixWitness := ⟨![273#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,66#9,68#9,8#9,272#9,96#9,128#9]⟩
theorem matrix135_dual : matrix135.DualCheck := by decide
noncomputable def extension135 : FrameExtension frame135 :=
  matrix135.extension matrix135_dual frame135 (by decide) (by decide)

def matrix136 : MatrixWitness := ⟨![196#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,34#9,132#9,8#9,48#9,192#9,256#9]⟩
theorem matrix136_dual : matrix136.DualCheck := by decide
noncomputable def extension136 : FrameExtension frame136 :=
  matrix136.extension matrix136_dual frame136 (by decide) (by decide)

def matrix137 : MatrixWitness := ⟨![145#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,193#9,2#9,68#9,8#9,208#9,32#9,256#9]⟩
theorem matrix137_dual : matrix137.DualCheck := by decide
noncomputable def extension137 : FrameExtension frame137 :=
  matrix137.extension matrix137_dual frame137 (by decide) (by decide)

def matrix138 : MatrixWitness := ⟨![162#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,1#9,194#9,68#9,8#9,16#9,224#9,256#9]⟩
theorem matrix138_dual : matrix138.DualCheck := by decide
noncomputable def extension138 : FrameExtension frame138 :=
  matrix138.extension matrix138_dual frame138 (by decide) (by decide)

def matrix139 : MatrixWitness := ⟨![145#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,129#9,66#9,68#9,8#9,144#9,96#9,256#9]⟩
theorem matrix139_dual : matrix139.DualCheck := by decide
noncomputable def extension139 : FrameExtension frame139 :=
  matrix139.extension matrix139_dual frame139 (by decide) (by decide)

def matrix140 : MatrixWitness := ⟨![162#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,65#9,130#9,68#9,8#9,80#9,160#9,256#9]⟩
theorem matrix140_dual : matrix140.DualCheck := by decide
noncomputable def extension140 : FrameExtension frame140 :=
  matrix140.extension matrix140_dual frame140 (by decide) (by decide)

def matrix141 : MatrixWitness := ⟨![290#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,322#9,68#9,8#9,16#9,352#9,128#9]⟩
theorem matrix141_dual : matrix141.DualCheck := by decide
noncomputable def extension141 : FrameExtension frame141 :=
  matrix141.extension matrix141_dual frame141 (by decide) (by decide)

def matrix142 : MatrixWitness := ⟨![273#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,321#9,2#9,68#9,8#9,336#9,32#9,128#9]⟩
theorem matrix142_dual : matrix142.DualCheck := by decide
noncomputable def extension142 : FrameExtension frame142 :=
  matrix142.extension matrix142_dual frame142 (by decide) (by decide)

def matrix143 : MatrixWitness := ⟨![145#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,161#9,34#9,4#9,8#9,176#9,64#9,256#9]⟩
theorem matrix143_dual : matrix143.DualCheck := by decide
noncomputable def extension143 : FrameExtension frame143 :=
  matrix143.extension matrix143_dual frame143 (by decide) (by decide)

def matrix144 : MatrixWitness := ⟨![273#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,289#9,34#9,4#9,8#9,304#9,64#9,128#9]⟩
theorem matrix144_dual : matrix144.DualCheck := by decide
noncomputable def extension144 : FrameExtension frame144 :=
  matrix144.extension matrix144_dual frame144 (by decide) (by decide)

def matrix145 : MatrixWitness := ⟨![273#9,162#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,321#9,130#9,68#9,8#9,336#9,160#9]⟩
theorem matrix145_dual : matrix145.DualCheck := by decide
noncomputable def extension145 : FrameExtension frame145 :=
  matrix145.extension matrix145_dual frame145 (by decide) (by decide)

def matrix146 : MatrixWitness := ⟨![290#9,145#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,193#9,258#9,68#9,8#9,208#9,288#9]⟩
theorem matrix146_dual : matrix146.DualCheck := by decide
noncomputable def extension146 : FrameExtension frame146 :=
  matrix146.extension matrix146_dual frame146 (by decide) (by decide)

def matrix147 : MatrixWitness := ⟨![290#9,162#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,450#9,68#9,8#9,16#9,480#9]⟩
theorem matrix147_dual : matrix147.DualCheck := by decide
noncomputable def extension147 : FrameExtension frame147 :=
  matrix147.extension matrix147_dual frame147 (by decide) (by decide)

def matrix148 : MatrixWitness := ⟨![273#9,145#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,385#9,66#9,68#9,8#9,400#9,96#9]⟩
theorem matrix148_dual : matrix148.DualCheck := by decide
noncomputable def extension148 : FrameExtension frame148 :=
  matrix148.extension matrix148_dual frame148 (by decide) (by decide)

def matrix149 : MatrixWitness := ⟨![290#9,145#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,129#9,322#9,68#9,8#9,144#9,352#9]⟩
theorem matrix149_dual : matrix149.DualCheck := by decide
noncomputable def extension149 : FrameExtension frame149 :=
  matrix149.extension matrix149_dual frame149 (by decide) (by decide)

def matrix150 : MatrixWitness := ⟨![273#9,162#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,257#9,194#9,68#9,8#9,272#9,224#9]⟩
theorem matrix150_dual : matrix150.DualCheck := by decide
noncomputable def extension150 : FrameExtension frame150 :=
  matrix150.extension matrix150_dual frame150 (by decide) (by decide)

def matrix151 : MatrixWitness := ⟨![273#9,145#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,449#9,2#9,68#9,8#9,464#9,32#9]⟩
theorem matrix151_dual : matrix151.DualCheck := by decide
noncomputable def extension151 : FrameExtension frame151 :=
  matrix151.extension matrix151_dual frame151 (by decide) (by decide)

def matrix152 : MatrixWitness := ⟨![290#9,162#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,65#9,386#9,68#9,8#9,80#9,416#9]⟩
theorem matrix152_dual : matrix152.DualCheck := by decide
noncomputable def extension152 : FrameExtension frame152 :=
  matrix152.extension matrix152_dual frame152 (by decide) (by decide)

def matrix153 : MatrixWitness := ⟨![273#9,145#9,85#9,51#9,1#9,2#9,4#9,8#9,16#9], ![256#9,128#9,64#9,32#9,481#9,34#9,68#9,8#9,496#9]⟩
theorem matrix153_dual : matrix153.DualCheck := by decide
noncomputable def extension153 : FrameExtension frame153 :=
  matrix153.extension matrix153_dual frame153 (by decide) (by decide)

def matrix154 : MatrixWitness := ⟨![487#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,8#9,16#9,288#9,320#9,384#9]⟩
theorem matrix154_dual : matrix154.DualCheck := by decide
noncomputable def extension154 : FrameExtension frame154 :=
  matrix154.extension matrix154_dual frame154 (by decide) (by decide)

def matrix155 : MatrixWitness := ⟨![84#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,2#9,68#9,8#9,80#9,32#9,128#9,256#9]⟩
theorem matrix155_dual : matrix155.DualCheck := by decide
noncomputable def extension155 : FrameExtension frame155 :=
  matrix155.extension matrix155_dual frame155 (by decide) (by decide)

def matrix156 : MatrixWitness := ⟨![74#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,66#9,4#9,72#9,16#9,32#9,128#9,256#9]⟩
theorem matrix156_dual : matrix156.DualCheck := by decide
noncomputable def extension156 : FrameExtension frame156 :=
  matrix156.extension matrix156_dual frame156 (by decide) (by decide)

def matrix157 : MatrixWitness := ⟨![505#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,4#9,264#9,272#9,288#9,320#9,384#9]⟩
theorem matrix157_dual : matrix157.DualCheck := by decide
noncomputable def extension157 : FrameExtension frame157 :=
  matrix157.extension matrix157_dual frame157 (by decide) (by decide)

def matrix158 : MatrixWitness := ⟨![44#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,1#9,2#9,36#9,40#9,16#9,64#9,128#9,256#9]⟩
theorem matrix158_dual : matrix158.DualCheck := by decide
noncomputable def extension158 : FrameExtension frame158 :=
  matrix158.extension matrix158_dual frame158 (by decide) (by decide)

def matrix159 : MatrixWitness := ⟨![415#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,264#9,272#9,32#9,64#9,384#9]⟩
theorem matrix159_dual : matrix159.DualCheck := by decide
noncomputable def extension159 : FrameExtension frame159 :=
  matrix159.extension matrix159_dual frame159 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
