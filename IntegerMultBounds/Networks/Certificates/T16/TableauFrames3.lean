module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix96 : MatrixWitness := ⟨![41#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,33#9,2#9,4#9,40#9,16#9,64#9,128#9,256#9]⟩
theorem matrix96_dual : matrix96.DualCheck := by decide
noncomputable def extension96 : FrameExtension frame96 :=
  matrix96.extension matrix96_dual frame96 (by decide) (by decide)

def matrix97 : MatrixWitness := ⟨![439#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,8#9,272#9,288#9,64#9,384#9]⟩
theorem matrix97_dual : matrix97.DualCheck := by decide
noncomputable def extension97 : FrameExtension frame97 :=
  matrix97.extension matrix97_dual frame97 (by decide) (by decide)

def matrix98 : MatrixWitness := ⟨![388#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,260#9,8#9,16#9,32#9,64#9,384#9]⟩
theorem matrix98_dual : matrix98.DualCheck := by decide
noncomputable def extension98 : FrameExtension frame98 :=
  matrix98.extension matrix98_dual frame98 (by decide) (by decide)

def matrix99 : MatrixWitness := ⟨![26#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9,256#9], ![16#9,1#9,18#9,4#9,24#9,32#9,64#9,128#9,256#9]⟩
theorem matrix99_dual : matrix99.DualCheck := by decide
noncomputable def extension99 : FrameExtension frame99 :=
  matrix99.extension matrix99_dual frame99 (by decide) (by decide)

def matrix100 : MatrixWitness := ⟨![463#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,264#9,16#9,32#9,320#9,384#9]⟩
theorem matrix100_dual : matrix100.DualCheck := by decide
noncomputable def extension100 : FrameExtension frame100 :=
  matrix100.extension matrix100_dual frame100 (by decide) (by decide)

def matrix101 : MatrixWitness := ⟨![81#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,65#9,2#9,4#9,8#9,80#9,32#9,128#9,256#9]⟩
theorem matrix101_dual : matrix101.DualCheck := by decide
noncomputable def extension101 : FrameExtension frame101 :=
  matrix101.extension matrix101_dual frame101 (by decide) (by decide)

def matrix102 : MatrixWitness := ⟨![98#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,66#9,4#9,8#9,16#9,96#9,128#9,256#9]⟩
theorem matrix102_dual : matrix102.DualCheck := by decide
noncomputable def extension102 : FrameExtension frame102 :=
  matrix102.extension matrix102_dual frame102 (by decide) (by decide)

def matrix103 : MatrixWitness := ⟨![508#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,260#9,264#9,272#9,288#9,320#9,384#9]⟩
theorem matrix103_dual : matrix103.DualCheck := by decide
noncomputable def extension103 : FrameExtension frame103 :=
  matrix103.extension matrix103_dual frame103 (by decide) (by decide)

def matrix104 : MatrixWitness := ⟨![41#9,26#9,1#9,2#9,4#9,8#9,64#9,128#9,256#9], ![32#9,16#9,33#9,18#9,4#9,56#9,64#9,128#9,256#9]⟩
theorem matrix104_dual : matrix104.DualCheck := by decide
noncomputable def extension104 : FrameExtension frame104 :=
  matrix104.extension matrix104_dual frame104 (by decide) (by decide)

def matrix105 : MatrixWitness := ⟨![81#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,2#9,4#9,40#9,80#9,128#9,256#9]⟩
theorem matrix105_dual : matrix105.DualCheck := by decide
noncomputable def extension105 : FrameExtension frame105 :=
  matrix105.extension matrix105_dual frame105 (by decide) (by decide)

def matrix106 : MatrixWitness := ⟨![75#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,66#9,4#9,104#9,16#9,128#9,256#9]⟩
theorem matrix106_dual : matrix106.DualCheck := by decide
noncomputable def extension106 : FrameExtension frame106 :=
  matrix106.extension matrix106_dual frame106 (by decide) (by decide)

def matrix107 : MatrixWitness := ⟨![388#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,34#9,260#9,8#9,48#9,64#9,384#9]⟩
theorem matrix107_dual : matrix107.DualCheck := by decide
noncomputable def extension107 : FrameExtension frame107 :=
  matrix107.extension matrix107_dual frame107 (by decide) (by decide)

def matrix108 : MatrixWitness := ⟨![439#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,258#9,260#9,72#9,336#9,352#9,384#9]⟩
theorem matrix108_dual : matrix108.DualCheck := by decide
noncomputable def extension108 : FrameExtension frame108 :=
  matrix108.extension matrix108_dual frame108 (by decide) (by decide)

def matrix109 : MatrixWitness := ⟨![439#9,75#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,321#9,322#9,260#9,72#9,272#9,288#9,384#9]⟩
theorem matrix109_dual : matrix109.DualCheck := by decide
noncomputable def extension109 : FrameExtension frame109 :=
  matrix109.extension matrix109_dual frame109 (by decide) (by decide)

def matrix110 : MatrixWitness := ⟨![388#9,75#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,65#9,66#9,260#9,72#9,16#9,32#9,384#9]⟩
theorem matrix110_dual : matrix110.DualCheck := by decide
noncomputable def extension110 : FrameExtension frame110 :=
  matrix110.extension matrix110_dual frame110 (by decide) (by decide)

def matrix111 : MatrixWitness := ⟨![388#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,2#9,260#9,72#9,80#9,96#9,384#9]⟩
theorem matrix111_dual : matrix111.DualCheck := by decide
noncomputable def extension111 : FrameExtension frame111 :=
  matrix111.extension matrix111_dual frame111 (by decide) (by decide)

def matrix112 : MatrixWitness := ⟨![75#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9,256#9], ![64#9,16#9,65#9,82#9,4#9,88#9,32#9,128#9,256#9]⟩
theorem matrix112_dual : matrix112.DualCheck := by decide
noncomputable def extension112 : FrameExtension frame112 :=
  matrix112.extension matrix112_dual frame112 (by decide) (by decide)

def matrix113 : MatrixWitness := ⟨![98#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9,256#9], ![64#9,16#9,1#9,82#9,4#9,24#9,96#9,128#9,256#9]⟩
theorem matrix113_dual : matrix113.DualCheck := by decide
noncomputable def extension113 : FrameExtension frame113 :=
  matrix113.extension matrix113_dual frame113 (by decide) (by decide)

def matrix114 : MatrixWitness := ⟨![463#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,289#9,290#9,260#9,264#9,48#9,320#9,384#9]⟩
theorem matrix114_dual : matrix114.DualCheck := by decide
noncomputable def extension114 : FrameExtension frame114 :=
  matrix114.extension matrix114_dual frame114 (by decide) (by decide)

def matrix115 : MatrixWitness := ⟨![81#9,51#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,34#9,4#9,8#9,112#9,128#9,256#9]⟩
theorem matrix115_dual : matrix115.DualCheck := by decide
noncomputable def extension115 : FrameExtension frame115 :=
  matrix115.extension matrix115_dual frame115 (by decide) (by decide)

def matrix116 : MatrixWitness := ⟨![388#9,98#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9], ![256#9,64#9,16#9,1#9,82#9,260#9,24#9,96#9,384#9]⟩
theorem matrix116_dual : matrix116.DualCheck := by decide
noncomputable def extension116 : FrameExtension frame116 :=
  matrix116.extension matrix116_dual frame116 (by decide) (by decide)

def matrix117 : MatrixWitness := ⟨![414#9,81#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,258#9,260#9,296#9,336#9,384#9]⟩
theorem matrix117_dual : matrix117.DualCheck := by decide
noncomputable def extension117 : FrameExtension frame117 :=
  matrix117.extension matrix117_dual frame117 (by decide) (by decide)

def matrix118 : MatrixWitness := ⟨![429#9,75#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9], ![256#9,64#9,16#9,321#9,82#9,260#9,344#9,288#9,384#9]⟩
theorem matrix118_dual : matrix118.DualCheck := by decide
noncomputable def extension118 : FrameExtension frame118 :=
  matrix118.extension matrix118_dual frame118 (by decide) (by decide)

def matrix119 : MatrixWitness := ⟨![388#9,75#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,66#9,260#9,104#9,16#9,384#9]⟩
theorem matrix119_dual : matrix119.DualCheck := by decide
noncomputable def extension119 : FrameExtension frame119 :=
  matrix119.extension matrix119_dual frame119 (by decide) (by decide)

def matrix120 : MatrixWitness := ⟨![388#9,75#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9], ![256#9,64#9,16#9,65#9,82#9,260#9,88#9,32#9,384#9]⟩
theorem matrix120_dual : matrix120.DualCheck := by decide
noncomputable def extension120 : FrameExtension frame120 :=
  matrix120.extension matrix120_dual frame120 (by decide) (by decide)

def matrix121 : MatrixWitness := ⟨![414#9,75#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,322#9,260#9,360#9,272#9,384#9]⟩
theorem matrix121_dual : matrix121.DualCheck := by decide
noncomputable def extension121 : FrameExtension frame121 :=
  matrix121.extension matrix121_dual frame121 (by decide) (by decide)

def matrix122 : MatrixWitness := ⟨![429#9,98#9,26#9,1#9,2#9,4#9,8#9,32#9,128#9], ![256#9,64#9,16#9,257#9,82#9,260#9,280#9,352#9,384#9]⟩
theorem matrix122_dual : matrix122.DualCheck := by decide
noncomputable def extension122 : FrameExtension frame122 :=
  matrix122.extension matrix122_dual frame122 (by decide) (by decide)

def matrix123 : MatrixWitness := ⟨![388#9,81#9,41#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,2#9,260#9,40#9,80#9,384#9]⟩
theorem matrix123_dual : matrix123.DualCheck := by decide
noncomputable def extension123 : FrameExtension frame123 :=
  matrix123.extension matrix123_dual frame123 (by decide) (by decide)

def matrix124 : MatrixWitness := ⟨![388#9,75#9,41#9,26#9,1#9,2#9,4#9,8#9,128#9], ![256#9,64#9,32#9,16#9,97#9,82#9,260#9,120#9,384#9]⟩
theorem matrix124_dual : matrix124.DualCheck := by decide
noncomputable def extension124 : FrameExtension frame124 :=
  matrix124.extension matrix124_dual frame124 (by decide) (by decide)

def matrix125 : MatrixWitness := ⟨![375#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,8#9,272#9,288#9,320#9,128#9]⟩
theorem matrix125_dual : matrix125.DualCheck := by decide
noncomputable def extension125 : FrameExtension frame125 :=
  matrix125.extension matrix125_dual frame125 (by decide) (by decide)

def matrix126 : MatrixWitness := ⟨![196#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,2#9,132#9,8#9,16#9,32#9,192#9,256#9]⟩
theorem matrix126_dual : matrix126.DualCheck := by decide
noncomputable def extension126 : FrameExtension frame126 :=
  matrix126.extension matrix126_dual frame126 (by decide) (by decide)

def matrix127 : MatrixWitness := ⟨![247#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,130#9,132#9,8#9,144#9,160#9,192#9,256#9]⟩
theorem matrix127_dual : matrix127.DualCheck := by decide
noncomputable def extension127 : FrameExtension frame127 :=
  matrix127.extension matrix127_dual frame127 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
