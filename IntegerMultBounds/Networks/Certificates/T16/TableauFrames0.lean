module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix0 : MatrixWitness := ⟨![1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9,256#9], ![1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9,256#9]⟩
theorem matrix0_dual : matrix0.DualCheck := by decide
noncomputable def extension0 : FrameExtension frame0 :=
  matrix0.extension matrix0_dual frame0 (by decide) (by decide)

def matrix1 : MatrixWitness := ⟨![256#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9,1#9], ![256#9,128#9,64#9,32#9,16#9,8#9,4#9,2#9,1#9]⟩
theorem matrix1_dual : matrix1.DualCheck := by decide
noncomputable def extension1 : FrameExtension frame1 :=
  matrix1.extension matrix1_dual frame1 (by decide) (by decide)

def matrix2 : MatrixWitness := ⟨![30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9,256#9], ![16#9,1#9,18#9,20#9,24#9,32#9,64#9,128#9,256#9]⟩
theorem matrix2_dual : matrix2.DualCheck := by decide
noncomputable def extension2 : FrameExtension frame2 :=
  matrix2.extension matrix2_dual frame2 (by decide) (by decide)

def matrix3 : MatrixWitness := ⟨![51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,33#9,34#9,4#9,8#9,48#9,64#9,128#9,256#9]⟩
theorem matrix3_dual : matrix3.DualCheck := by decide
noncomputable def extension3 : FrameExtension frame3 :=
  matrix3.extension matrix3_dual frame3 (by decide) (by decide)

def matrix4 : MatrixWitness := ⟨![459#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,4#9,264#9,16#9,32#9,320#9,384#9]⟩
theorem matrix4_dual : matrix4.DualCheck := by decide
noncomputable def extension4 : FrameExtension frame4 :=
  matrix4.extension matrix4_dual frame4 (by decide) (by decide)

def matrix5 : MatrixWitness := ⟨![75#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,65#9,66#9,4#9,72#9,16#9,32#9,128#9,256#9]⟩
theorem matrix5_dual : matrix5.DualCheck := by decide
noncomputable def extension5 : FrameExtension frame5 :=
  matrix5.extension matrix5_dual frame5 (by decide) (by decide)

def matrix6 : MatrixWitness := ⟨![102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,66#9,68#9,8#9,16#9,96#9,128#9,256#9]⟩
theorem matrix6_dual : matrix6.DualCheck := by decide
noncomputable def extension6 : FrameExtension frame6 :=
  matrix6.extension matrix6_dual frame6 (by decide) (by decide)

def matrix7 : MatrixWitness := ⟨![120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,2#9,4#9,72#9,80#9,96#9,128#9,256#9]⟩
theorem matrix7_dual : matrix7.DualCheck := by decide
noncomputable def extension7 : FrameExtension frame7 :=
  matrix7.extension matrix7_dual frame7 (by decide) (by decide)

def matrix8 : MatrixWitness := ⟨![85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,65#9,2#9,68#9,8#9,80#9,32#9,128#9,256#9]⟩
theorem matrix8_dual : matrix8.DualCheck := by decide
noncomputable def extension8 : FrameExtension frame8 :=
  matrix8.extension matrix8_dual frame8 (by decide) (by decide)

def matrix9 : MatrixWitness := ⟨![11#9,1#9,2#9,4#9,16#9,32#9,64#9,128#9,256#9], ![8#9,9#9,10#9,4#9,16#9,32#9,64#9,128#9,256#9]⟩
theorem matrix9_dual : matrix9.DualCheck := by decide
noncomputable def extension9 : FrameExtension frame9 :=
  matrix9.extension matrix9_dual frame9 (by decide) (by decide)

def matrix10 : MatrixWitness := ⟨![448#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,4#9,8#9,16#9,32#9,320#9,384#9]⟩
theorem matrix10_dual : matrix10.DualCheck := by decide
noncomputable def extension10 : FrameExtension frame10 :=
  matrix10.extension matrix10_dual frame10 (by decide) (by decide)

def matrix11 : MatrixWitness := ⟨![493#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,260#9,264#9,16#9,288#9,320#9,384#9]⟩
theorem matrix11_dual : matrix11.DualCheck := by decide
noncomputable def extension11 : FrameExtension frame11 :=
  matrix11.extension matrix11_dual frame11 (by decide) (by decide)

def matrix12 : MatrixWitness := ⟨![38#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,1#9,34#9,36#9,8#9,16#9,64#9,128#9,256#9]⟩
theorem matrix12_dual : matrix12.DualCheck := by decide
noncomputable def extension12 : FrameExtension frame12 :=
  matrix12.extension matrix12_dual frame12 (by decide) (by decide)

def matrix13 : MatrixWitness := ⟨![499#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,4#9,8#9,272#9,288#9,320#9,384#9]⟩
theorem matrix13_dual : matrix13.DualCheck := by decide
noncomputable def extension13 : FrameExtension frame13 :=
  matrix13.extension matrix13_dual frame13 (by decide) (by decide)

def matrix14 : MatrixWitness := ⟨![56#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,1#9,2#9,4#9,40#9,48#9,64#9,128#9,256#9]⟩
theorem matrix14_dual : matrix14.DualCheck := by decide
noncomputable def extension14 : FrameExtension frame14 :=
  matrix14.extension matrix14_dual frame14 (by decide) (by decide)

def matrix15 : MatrixWitness := ⟨![21#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9,256#9], ![16#9,17#9,2#9,20#9,8#9,32#9,64#9,128#9,256#9]⟩
theorem matrix15_dual : matrix15.DualCheck := by decide
noncomputable def extension15 : FrameExtension frame15 :=
  matrix15.extension matrix15_dual frame15 (by decide) (by decide)

def matrix16 : MatrixWitness := ⟨![478#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,260#9,264#9,272#9,32#9,320#9,384#9]⟩
theorem matrix16_dual : matrix16.DualCheck := by decide
noncomputable def extension16 : FrameExtension frame16 :=
  matrix16.extension matrix16_dual frame16 (by decide) (by decide)

def matrix17 : MatrixWitness := ⟨![38#9,11#9,1#9,2#9,4#9,16#9,64#9,128#9,256#9], ![32#9,8#9,9#9,42#9,36#9,16#9,64#9,128#9,256#9]⟩
theorem matrix17_dual : matrix17.DualCheck := by decide
noncomputable def extension17 : FrameExtension frame17 :=
  matrix17.extension matrix17_dual frame17 (by decide) (by decide)

def matrix18 : MatrixWitness := ⟨![51#9,11#9,1#9,2#9,4#9,16#9,64#9,128#9,256#9], ![32#9,8#9,41#9,42#9,4#9,48#9,64#9,128#9,256#9]⟩
theorem matrix18_dual : matrix18.DualCheck := by decide
noncomputable def extension18 : FrameExtension frame18 :=
  matrix18.extension matrix18_dual frame18 (by decide) (by decide)

def matrix19 : MatrixWitness := ⟨![21#9,11#9,1#9,2#9,4#9,32#9,64#9,128#9,256#9], ![16#9,8#9,25#9,10#9,20#9,32#9,64#9,128#9,256#9]⟩
theorem matrix19_dual : matrix19.DualCheck := by decide
noncomputable def extension19 : FrameExtension frame19 :=
  matrix19.extension matrix19_dual frame19 (by decide) (by decide)

def matrix20 : MatrixWitness := ⟨![448#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,2#9,36#9,40#9,16#9,320#9,384#9]⟩
theorem matrix20_dual : matrix20.DualCheck := by decide
noncomputable def extension20 : FrameExtension frame20 :=
  matrix20.extension matrix20_dual frame20 (by decide) (by decide)

def matrix21 : MatrixWitness := ⟨![448#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,34#9,4#9,8#9,48#9,320#9,384#9]⟩
theorem matrix21_dual : matrix21.DualCheck := by decide
noncomputable def extension21 : FrameExtension frame21 :=
  matrix21.extension matrix21_dual frame21 (by decide) (by decide)

def matrix22 : MatrixWitness := ⟨![448#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,1#9,18#9,20#9,24#9,32#9,320#9,384#9]⟩
theorem matrix22_dual : matrix22.DualCheck := by decide
noncomputable def extension22 : FrameExtension frame22 :=
  matrix22.extension matrix22_dual frame22 (by decide) (by decide)

def matrix23 : MatrixWitness := ⟨![493#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,257#9,18#9,276#9,280#9,288#9,320#9,384#9]⟩
theorem matrix23_dual : matrix23.DualCheck := by decide
noncomputable def extension23 : FrameExtension frame23 :=
  matrix23.extension matrix23_dual frame23 (by decide) (by decide)

def matrix24 : MatrixWitness := ⟨![478#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,290#9,260#9,264#9,304#9,320#9,384#9]⟩
theorem matrix24_dual : matrix24.DualCheck := by decide
noncomputable def extension24 : FrameExtension frame24 :=
  matrix24.extension matrix24_dual frame24 (by decide) (by decide)

def matrix25 : MatrixWitness := ⟨![38#9,30#9,1#9,2#9,4#9,8#9,64#9,128#9,256#9], ![32#9,16#9,1#9,50#9,52#9,24#9,64#9,128#9,256#9]⟩
theorem matrix25_dual : matrix25.DualCheck := by decide
noncomputable def extension25 : FrameExtension frame25 :=
  matrix25.extension matrix25_dual frame25 (by decide) (by decide)

def matrix26 : MatrixWitness := ⟨![38#9,21#9,1#9,2#9,4#9,8#9,64#9,128#9,256#9], ![32#9,16#9,17#9,34#9,52#9,8#9,64#9,128#9,256#9]⟩
theorem matrix26_dual : matrix26.DualCheck := by decide
noncomputable def extension26 : FrameExtension frame26 :=
  matrix26.extension matrix26_dual frame26 (by decide) (by decide)

def matrix27 : MatrixWitness := ⟨![478#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,258#9,292#9,296#9,272#9,320#9,384#9]⟩
theorem matrix27_dual : matrix27.DualCheck := by decide
noncomputable def extension27 : FrameExtension frame27 :=
  matrix27.extension matrix27_dual frame27 (by decide) (by decide)

def matrix28 : MatrixWitness := ⟨![45#9,21#9,1#9,2#9,4#9,8#9,64#9,128#9,256#9], ![32#9,16#9,49#9,2#9,52#9,40#9,64#9,128#9,256#9]⟩
theorem matrix28_dual : matrix28.DualCheck := by decide
noncomputable def extension28 : FrameExtension frame28 :=
  matrix28.extension matrix28_dual frame28 (by decide) (by decide)

def matrix29 : MatrixWitness := ⟨![459#9,38#9,21#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,273#9,290#9,52#9,264#9,320#9,384#9]⟩
theorem matrix29_dual : matrix29.DualCheck := by decide
noncomputable def extension29 : FrameExtension frame29 :=
  matrix29.extension matrix29_dual frame29 (by decide) (by decide)

def matrix30 : MatrixWitness := ⟨![448#9,51#9,11#9,1#9,2#9,4#9,16#9,64#9,128#9], ![256#9,32#9,8#9,41#9,42#9,4#9,48#9,320#9,384#9]⟩
theorem matrix30_dual : matrix30.DualCheck := by decide
noncomputable def extension30 : FrameExtension frame30 :=
  matrix30.extension matrix30_dual frame30 (by decide) (by decide)

def matrix31 : MatrixWitness := ⟨![448#9,38#9,30#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,1#9,50#9,52#9,24#9,320#9,384#9]⟩
theorem matrix31_dual : matrix31.DualCheck := by decide
noncomputable def extension31 : FrameExtension frame31 :=
  matrix31.extension matrix31_dual frame31 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
