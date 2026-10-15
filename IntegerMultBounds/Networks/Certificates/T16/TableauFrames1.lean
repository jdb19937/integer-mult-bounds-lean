module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix32 : MatrixWitness := ⟨![486#9,21#9,11#9,1#9,2#9,4#9,32#9,64#9,128#9], ![256#9,16#9,8#9,25#9,266#9,276#9,288#9,320#9,384#9]⟩
theorem matrix32_dual : matrix32.DualCheck := by decide
noncomputable def extension32 : FrameExtension frame32 :=
  matrix32.extension matrix32_dual frame32 (by decide) (by decide)

def matrix33 : MatrixWitness := ⟨![459#9,38#9,30#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,257#9,306#9,52#9,280#9,320#9,384#9]⟩
theorem matrix33_dual : matrix33.DualCheck := by decide
noncomputable def extension33 : FrameExtension frame33 :=
  matrix33.extension matrix33_dual frame33 (by decide) (by decide)

def matrix34 : MatrixWitness := ⟨![448#9,21#9,11#9,1#9,2#9,4#9,32#9,64#9,128#9], ![256#9,16#9,8#9,25#9,10#9,20#9,32#9,320#9,384#9]⟩
theorem matrix34_dual : matrix34.DualCheck := by decide
noncomputable def extension34 : FrameExtension frame34 :=
  matrix34.extension matrix34_dual frame34 (by decide) (by decide)

def matrix35 : MatrixWitness := ⟨![448#9,38#9,21#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,17#9,34#9,52#9,8#9,320#9,384#9]⟩
theorem matrix35_dual : matrix35.DualCheck := by decide
noncomputable def extension35 : FrameExtension frame35 :=
  matrix35.extension matrix35_dual frame35 (by decide) (by decide)

def matrix36 : MatrixWitness := ⟨![469#9,51#9,11#9,1#9,2#9,4#9,16#9,64#9,128#9], ![256#9,32#9,8#9,297#9,42#9,260#9,304#9,320#9,384#9]⟩
theorem matrix36_dual : matrix36.DualCheck := by decide
noncomputable def extension36 : FrameExtension frame36 :=
  matrix36.extension matrix36_dual frame36 (by decide) (by decide)

def matrix37 : MatrixWitness := ⟨![448#9,38#9,21#9,11#9,1#9,2#9,4#9,64#9,128#9], ![256#9,32#9,16#9,8#9,25#9,42#9,52#9,320#9,384#9]⟩
theorem matrix37_dual : matrix37.DualCheck := by decide
noncomputable def extension37 : FrameExtension frame37 :=
  matrix37.extension matrix37_dual frame37 (by decide) (by decide)

def matrix38 : MatrixWitness := ⟨![208#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,2#9,4#9,8#9,144#9,32#9,192#9,256#9]⟩
theorem matrix38_dual : matrix38.DualCheck := by decide
noncomputable def extension38 : FrameExtension frame38 :=
  matrix38.extension matrix38_dual frame38 (by decide) (by decide)

def matrix39 : MatrixWitness := ⟨![336#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,4#9,8#9,272#9,32#9,320#9,128#9]⟩
theorem matrix39_dual : matrix39.DualCheck := by decide
noncomputable def extension39 : FrameExtension frame39 :=
  matrix39.extension matrix39_dual frame39 (by decide) (by decide)

def matrix40 : MatrixWitness := ⟨![381#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,260#9,264#9,272#9,288#9,320#9,128#9]⟩
theorem matrix40_dual : matrix40.DualCheck := by decide
noncomputable def extension40 : FrameExtension frame40 :=
  matrix40.extension matrix40_dual frame40 (by decide) (by decide)

def matrix41 : MatrixWitness := ⟨![253#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,2#9,132#9,136#9,144#9,160#9,192#9,256#9]⟩
theorem matrix41_dual : matrix41.DualCheck := by decide
noncomputable def extension41 : FrameExtension frame41 :=
  matrix41.extension matrix41_dual frame41 (by decide) (by decide)

def matrix42 : MatrixWitness := ⟨![296#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,4#9,264#9,16#9,288#9,64#9,128#9]⟩
theorem matrix42_dual : matrix42.DualCheck := by decide
noncomputable def extension42 : FrameExtension frame42 :=
  matrix42.extension matrix42_dual frame42 (by decide) (by decide)

def matrix43 : MatrixWitness := ⟨![168#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,2#9,4#9,136#9,16#9,160#9,64#9,256#9]⟩
theorem matrix43_dual : matrix43.DualCheck := by decide
noncomputable def extension43 : FrameExtension frame43 :=
  matrix43.extension matrix43_dual frame43 (by decide) (by decide)

def matrix44 : MatrixWitness := ⟨![133#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,2#9,132#9,8#9,16#9,32#9,64#9,256#9]⟩
theorem matrix44_dual : matrix44.DualCheck := by decide
noncomputable def extension44 : FrameExtension frame44 :=
  matrix44.extension matrix44_dual frame44 (by decide) (by decide)

def matrix45 : MatrixWitness := ⟨![261#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,260#9,8#9,16#9,32#9,64#9,128#9]⟩
theorem matrix45_dual : matrix45.DualCheck := by decide
noncomputable def extension45 : FrameExtension frame45 :=
  matrix45.extension matrix45_dual frame45 (by decide) (by decide)

def matrix46 : MatrixWitness := ⟨![208#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,2#9,36#9,40#9,144#9,192#9,256#9]⟩
theorem matrix46_dual : matrix46.DualCheck := by decide
noncomputable def extension46 : FrameExtension frame46 :=
  matrix46.extension matrix46_dual frame46 (by decide) (by decide)

def matrix47 : MatrixWitness := ⟨![168#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,1#9,2#9,4#9,200#9,80#9,224#9,256#9]⟩
theorem matrix47_dual : matrix47.DualCheck := by decide
noncomputable def extension47 : FrameExtension frame47 :=
  matrix47.extension matrix47_dual frame47 (by decide) (by decide)

def matrix48 : MatrixWitness := ⟨![133#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,193#9,2#9,196#9,8#9,80#9,32#9,256#9]⟩
theorem matrix48_dual : matrix48.DualCheck := by decide
noncomputable def extension48 : FrameExtension frame48 :=
  matrix48.extension matrix48_dual frame48 (by decide) (by decide)

def matrix49 : MatrixWitness := ⟨![336#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,2#9,36#9,40#9,272#9,320#9,128#9]⟩
theorem matrix49_dual : matrix49.DualCheck := by decide
noncomputable def extension49 : FrameExtension frame49 :=
  matrix49.extension matrix49_dual frame49 (by decide) (by decide)

def matrix50 : MatrixWitness := ⟨![296#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,2#9,4#9,328#9,80#9,352#9,128#9]⟩
theorem matrix50_dual : matrix50.DualCheck := by decide
noncomputable def extension50 : FrameExtension frame50 :=
  matrix50.extension matrix50_dual frame50 (by decide) (by decide)

def matrix51 : MatrixWitness := ⟨![261#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,321#9,2#9,324#9,8#9,80#9,32#9,128#9]⟩
theorem matrix51_dual : matrix51.DualCheck := by decide
noncomputable def extension51 : FrameExtension frame51 :=
  matrix51.extension matrix51_dual frame51 (by decide) (by decide)

def matrix52 : MatrixWitness := ⟨![296#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,65#9,2#9,68#9,264#9,80#9,288#9,128#9]⟩
theorem matrix52_dual : matrix52.DualCheck := by decide
noncomputable def extension52 : FrameExtension frame52 :=
  matrix52.extension matrix52_dual frame52 (by decide) (by decide)

def matrix53 : MatrixWitness := ⟨![261#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,2#9,260#9,72#9,80#9,96#9,128#9]⟩
theorem matrix53_dual : matrix53.DualCheck := by decide
noncomputable def extension53 : FrameExtension frame53 :=
  matrix53.extension matrix53_dual frame53 (by decide) (by decide)

def matrix54 : MatrixWitness := ⟨![168#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,65#9,2#9,68#9,136#9,80#9,160#9,256#9]⟩
theorem matrix54_dual : matrix54.DualCheck := by decide
noncomputable def extension54 : FrameExtension frame54 :=
  matrix54.extension matrix54_dual frame54 (by decide) (by decide)

def matrix55 : MatrixWitness := ⟨![133#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,129#9,2#9,132#9,72#9,80#9,96#9,256#9]⟩
theorem matrix55_dual : matrix55.DualCheck := by decide
noncomputable def extension55 : FrameExtension frame55 :=
  matrix55.extension matrix55_dual frame55 (by decide) (by decide)

def matrix56 : MatrixWitness := ⟨![261#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,289#9,2#9,292#9,40#9,16#9,64#9,128#9]⟩
theorem matrix56_dual : matrix56.DualCheck := by decide
noncomputable def extension56 : FrameExtension frame56 :=
  matrix56.extension matrix56_dual frame56 (by decide) (by decide)

def matrix57 : MatrixWitness := ⟨![133#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,161#9,2#9,164#9,40#9,16#9,64#9,256#9]⟩
theorem matrix57_dual : matrix57.DualCheck := by decide
noncomputable def extension57 : FrameExtension frame57 :=
  matrix57.extension matrix57_dual frame57 (by decide) (by decide)

def matrix58 : MatrixWitness := ⟨![261#9,133#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,385#9,2#9,388#9,72#9,80#9,96#9]⟩
theorem matrix58_dual : matrix58.DualCheck := by decide
noncomputable def extension58 : FrameExtension frame58 :=
  matrix58.extension matrix58_dual frame58 (by decide) (by decide)

def matrix59 : MatrixWitness := ⟨![296#9,168#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,2#9,4#9,456#9,80#9,480#9]⟩
theorem matrix59_dual : matrix59.DualCheck := by decide
noncomputable def extension59 : FrameExtension frame59 :=
  matrix59.extension matrix59_dual frame59 (by decide) (by decide)

def matrix60 : MatrixWitness := ⟨![261#9,168#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,321#9,2#9,324#9,136#9,80#9,160#9]⟩
theorem matrix60_dual : matrix60.DualCheck := by decide
noncomputable def extension60 : FrameExtension frame60 :=
  matrix60.extension matrix60_dual frame60 (by decide) (by decide)

def matrix61 : MatrixWitness := ⟨![296#9,133#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,193#9,2#9,196#9,264#9,80#9,288#9]⟩
theorem matrix61_dual : matrix61.DualCheck := by decide
noncomputable def extension61 : FrameExtension frame61 :=
  matrix61.extension matrix61_dual frame61 (by decide) (by decide)

def matrix62 : MatrixWitness := ⟨![296#9,168#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,65#9,2#9,68#9,392#9,80#9,416#9]⟩
theorem matrix62_dual : matrix62.DualCheck := by decide
noncomputable def extension62 : FrameExtension frame62 :=
  matrix62.extension matrix62_dual frame62 (by decide) (by decide)

def matrix63 : MatrixWitness := ⟨![261#9,133#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,449#9,2#9,452#9,8#9,80#9,32#9]⟩
theorem matrix63_dual : matrix63.DualCheck := by decide
noncomputable def extension63 : FrameExtension frame63 :=
  matrix63.extension matrix63_dual frame63 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
