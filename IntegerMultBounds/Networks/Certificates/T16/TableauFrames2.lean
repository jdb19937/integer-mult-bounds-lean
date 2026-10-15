module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix64 : MatrixWitness := ⟨![296#9,133#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,129#9,2#9,132#9,328#9,80#9,352#9]⟩
theorem matrix64_dual : matrix64.DualCheck := by decide
noncomputable def extension64 : FrameExtension frame64 :=
  matrix64.extension matrix64_dual frame64 (by decide) (by decide)

def matrix65 : MatrixWitness := ⟨![261#9,168#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,257#9,2#9,260#9,200#9,80#9,224#9]⟩
theorem matrix65_dual : matrix65.DualCheck := by decide
noncomputable def extension65 : FrameExtension frame65 :=
  matrix65.extension matrix65_dual frame65 (by decide) (by decide)

def matrix66 : MatrixWitness := ⟨![261#9,133#9,85#9,45#9,1#9,2#9,4#9,8#9,16#9], ![256#9,128#9,64#9,32#9,481#9,2#9,484#9,40#9,80#9]⟩
theorem matrix66_dual : matrix66.DualCheck := by decide
noncomputable def extension66 : FrameExtension frame66 :=
  matrix66.extension matrix66_dual frame66 (by decide) (by decide)

def matrix67 : MatrixWitness := ⟨![400#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,4#9,8#9,272#9,32#9,64#9,384#9]⟩
theorem matrix67_dual : matrix67.DualCheck := by decide
noncomputable def extension67 : FrameExtension frame67 :=
  matrix67.extension matrix67_dual frame67 (by decide) (by decide)

def matrix68 : MatrixWitness := ⟨![35#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,33#9,34#9,4#9,8#9,16#9,64#9,128#9,256#9]⟩
theorem matrix68_dual : matrix68.DualCheck := by decide
noncomputable def extension68 : FrameExtension frame68 :=
  matrix68.extension matrix68_dual frame68 (by decide) (by decide)

def matrix69 : MatrixWitness := ⟨![14#9,1#9,2#9,4#9,16#9,32#9,64#9,128#9,256#9], ![8#9,1#9,10#9,12#9,16#9,32#9,64#9,128#9,256#9]⟩
theorem matrix69_dual : matrix69.DualCheck := by decide
noncomputable def extension69 : FrameExtension frame69 :=
  matrix69.extension matrix69_dual frame69 (by decide) (by decide)

def matrix70 : MatrixWitness := ⟨![445#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,260#9,264#9,272#9,288#9,64#9,384#9]⟩
theorem matrix70_dual : matrix70.DualCheck := by decide
noncomputable def extension70 : FrameExtension frame70 :=
  matrix70.extension matrix70_dual frame70 (by decide) (by decide)

def matrix71 : MatrixWitness := ⟨![104#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,2#9,4#9,72#9,16#9,96#9,128#9,256#9]⟩
theorem matrix71_dual : matrix71.DualCheck := by decide
noncomputable def extension71 : FrameExtension frame71 :=
  matrix71.extension matrix71_dual frame71 (by decide) (by decide)

def matrix72 : MatrixWitness := ⟨![475#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,4#9,264#9,272#9,32#9,320#9,384#9]⟩
theorem matrix72_dual : matrix72.DualCheck := by decide
noncomputable def extension72 : FrameExtension frame72 :=
  matrix72.extension matrix72_dual frame72 (by decide) (by decide)

def matrix73 : MatrixWitness := ⟨![502#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,260#9,8#9,272#9,288#9,320#9,384#9]⟩
theorem matrix73_dual : matrix73.DualCheck := by decide
noncomputable def extension73 : FrameExtension frame73 :=
  matrix73.extension matrix73_dual frame73 (by decide) (by decide)

def matrix74 : MatrixWitness := ⟨![69#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,65#9,2#9,68#9,8#9,16#9,32#9,128#9,256#9]⟩
theorem matrix74_dual : matrix74.DualCheck := by decide
noncomputable def extension74 : FrameExtension frame74 :=
  matrix74.extension matrix74_dual frame74 (by decide) (by decide)

def matrix75 : MatrixWitness := ⟨![400#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,2#9,36#9,40#9,272#9,64#9,384#9]⟩
theorem matrix75_dual : matrix75.DualCheck := by decide
noncomputable def extension75 : FrameExtension frame75 :=
  matrix75.extension matrix75_dual frame75 (by decide) (by decide)

def matrix76 : MatrixWitness := ⟨![400#9,75#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,65#9,66#9,4#9,72#9,272#9,32#9,384#9]⟩
theorem matrix76_dual : matrix76.DualCheck := by decide
noncomputable def extension76 : FrameExtension frame76 :=
  matrix76.extension matrix76_dual frame76 (by decide) (by decide)

def matrix77 : MatrixWitness := ⟨![400#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,66#9,68#9,8#9,272#9,96#9,384#9]⟩
theorem matrix77_dual : matrix77.DualCheck := by decide
noncomputable def extension77 : FrameExtension frame77 :=
  matrix77.extension matrix77_dual frame77 (by decide) (by decide)

def matrix78 : MatrixWitness := ⟨![35#9,14#9,1#9,2#9,4#9,16#9,64#9,128#9,256#9], ![32#9,8#9,33#9,42#9,12#9,16#9,64#9,128#9,256#9]⟩
theorem matrix78_dual : matrix78.DualCheck := by decide
noncomputable def extension78 : FrameExtension frame78 :=
  matrix78.extension matrix78_dual frame78 (by decide) (by decide)

def matrix79 : MatrixWitness := ⟨![75#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,98#9,4#9,72#9,16#9,128#9,256#9]⟩
theorem matrix79_dual : matrix79.DualCheck := by decide
noncomputable def extension79 : FrameExtension frame79 :=
  matrix79.extension matrix79_dual frame79 (by decide) (by decide)

def matrix80 : MatrixWitness := ⟨![69#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,34#9,68#9,8#9,16#9,128#9,256#9]⟩
theorem matrix80_dual : matrix80.DualCheck := by decide
noncomputable def extension80 : FrameExtension frame80 :=
  matrix80.extension matrix80_dual frame80 (by decide) (by decide)

def matrix81 : MatrixWitness := ⟨![102#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9,256#9], ![64#9,8#9,1#9,74#9,76#9,16#9,96#9,128#9,256#9]⟩
theorem matrix81_dual : matrix81.DualCheck := by decide
noncomputable def extension81 : FrameExtension frame81 :=
  matrix81.extension matrix81_dual frame81 (by decide) (by decide)

def matrix82 : MatrixWitness := ⟨![69#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9,256#9], ![64#9,8#9,65#9,10#9,76#9,16#9,32#9,128#9,256#9]⟩
theorem matrix82_dual : matrix82.DualCheck := by decide
noncomputable def extension82 : FrameExtension frame82 :=
  matrix82.extension matrix82_dual frame82 (by decide) (by decide)

def matrix83 : MatrixWitness := ⟨![445#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,66#9,324#9,264#9,272#9,352#9,384#9]⟩
theorem matrix83_dual : matrix83.DualCheck := by decide
noncomputable def extension83 : FrameExtension frame83 :=
  matrix83.extension matrix83_dual frame83 (by decide) (by decide)

def matrix84 : MatrixWitness := ⟨![445#9,75#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,321#9,66#9,260#9,328#9,272#9,288#9,384#9]⟩
theorem matrix84_dual : matrix84.DualCheck := by decide
noncomputable def extension84 : FrameExtension frame84 :=
  matrix84.extension matrix84_dual frame84 (by decide) (by decide)

def matrix85 : MatrixWitness := ⟨![69#9,45#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,2#9,100#9,40#9,16#9,128#9,256#9]⟩
theorem matrix85_dual : matrix85.DualCheck := by decide
noncomputable def extension85 : FrameExtension frame85 :=
  matrix85.extension matrix85_dual frame85 (by decide) (by decide)

def matrix86 : MatrixWitness := ⟨![475#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,289#9,258#9,36#9,296#9,272#9,320#9,384#9]⟩
theorem matrix86_dual : matrix86.DualCheck := by decide
noncomputable def extension86 : FrameExtension frame86 :=
  matrix86.extension matrix86_dual frame86 (by decide) (by decide)

def matrix87 : MatrixWitness := ⟨![435#9,69#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9], ![256#9,64#9,8#9,321#9,266#9,76#9,272#9,288#9,384#9]⟩
theorem matrix87_dual : matrix87.DualCheck := by decide
noncomputable def extension87 : FrameExtension frame87 :=
  matrix87.extension matrix87_dual frame87 (by decide) (by decide)

def matrix88 : MatrixWitness := ⟨![400#9,75#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,98#9,4#9,72#9,272#9,384#9]⟩
theorem matrix88_dual : matrix88.DualCheck := by decide
noncomputable def extension88 : FrameExtension frame88 :=
  matrix88.extension matrix88_dual frame88 (by decide) (by decide)

def matrix89 : MatrixWitness := ⟨![414#9,69#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,290#9,324#9,264#9,272#9,384#9]⟩
theorem matrix89_dual : matrix89.DualCheck := by decide
noncomputable def extension89 : FrameExtension frame89 :=
  matrix89.extension matrix89_dual frame89 (by decide) (by decide)

def matrix90 : MatrixWitness := ⟨![400#9,102#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9], ![256#9,64#9,8#9,1#9,74#9,76#9,272#9,96#9,384#9]⟩
theorem matrix90_dual : matrix90.DualCheck := by decide
noncomputable def extension90 : FrameExtension frame90 :=
  matrix90.extension matrix90_dual frame90 (by decide) (by decide)

def matrix91 : MatrixWitness := ⟨![435#9,102#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9], ![256#9,64#9,8#9,257#9,330#9,76#9,272#9,352#9,384#9]⟩
theorem matrix91_dual : matrix91.DualCheck := by decide
noncomputable def extension91 : FrameExtension frame91 :=
  matrix91.extension matrix91_dual frame91 (by decide) (by decide)

def matrix92 : MatrixWitness := ⟨![400#9,69#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,34#9,68#9,8#9,272#9,384#9]⟩
theorem matrix92_dual : matrix92.DualCheck := by decide
noncomputable def extension92 : FrameExtension frame92 :=
  matrix92.extension matrix92_dual frame92 (by decide) (by decide)

def matrix93 : MatrixWitness := ⟨![414#9,75#9,35#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,354#9,260#9,328#9,272#9,384#9]⟩
theorem matrix93_dual : matrix93.DualCheck := by decide
noncomputable def extension93 : FrameExtension frame93 :=
  matrix93.extension matrix93_dual frame93 (by decide) (by decide)

def matrix94 : MatrixWitness := ⟨![400#9,69#9,14#9,1#9,2#9,4#9,16#9,32#9,128#9], ![256#9,64#9,8#9,65#9,10#9,76#9,272#9,32#9,384#9]⟩
theorem matrix94_dual : matrix94.DualCheck := by decide
noncomputable def extension94 : FrameExtension frame94 :=
  matrix94.extension matrix94_dual frame94 (by decide) (by decide)

def matrix95 : MatrixWitness := ⟨![400#9,69#9,35#9,14#9,1#9,2#9,4#9,16#9,128#9], ![256#9,64#9,32#9,8#9,97#9,42#9,76#9,272#9,384#9]⟩
theorem matrix95_dual : matrix95.DualCheck := by decide
noncomputable def extension95 : FrameExtension frame95 :=
  matrix95.extension matrix95_dual frame95 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
