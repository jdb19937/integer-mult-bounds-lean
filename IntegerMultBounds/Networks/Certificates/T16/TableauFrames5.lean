module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix160 : MatrixWitness := ⟨![385#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,4#9,8#9,16#9,32#9,64#9,384#9]⟩
theorem matrix160_dual : matrix160.DualCheck := by decide
noncomputable def extension160 : FrameExtension frame160 :=
  matrix160.extension matrix160_dual frame160 (by decide) (by decide)

def matrix161 : MatrixWitness := ⟨![50#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,1#9,34#9,4#9,8#9,48#9,64#9,128#9,256#9]⟩
theorem matrix161_dual : matrix161.DualCheck := by decide
noncomputable def extension161 : FrameExtension frame161 :=
  matrix161.extension matrix161_dual frame161 (by decide) (by decide)

def matrix162 : MatrixWitness := ⟨![487#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,257#9,274#9,276#9,24#9,288#9,320#9,384#9]⟩
theorem matrix162_dual : matrix162.DualCheck := by decide
noncomputable def extension162 : FrameExtension frame162 :=
  matrix162.extension matrix162_dual frame162 (by decide) (by decide)

def matrix163 : MatrixWitness := ⟨![415#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,258#9,260#9,328#9,336#9,96#9,384#9]⟩
theorem matrix163_dual : matrix163.DualCheck := by decide
noncomputable def extension163 : FrameExtension frame163 :=
  matrix163.extension matrix163_dual frame163 (by decide) (by decide)

def matrix164 : MatrixWitness := ⟨![385#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,66#9,68#9,8#9,16#9,96#9,384#9]⟩
theorem matrix164_dual : matrix164.DualCheck := by decide
noncomputable def extension164 : FrameExtension frame164 :=
  matrix164.extension matrix164_dual frame164 (by decide) (by decide)

def matrix165 : MatrixWitness := ⟨![74#9,30#9,1#9,2#9,4#9,8#9,32#9,128#9,256#9], ![64#9,16#9,1#9,82#9,20#9,88#9,32#9,128#9,256#9]⟩
theorem matrix165_dual : matrix165.DualCheck := by decide
noncomputable def extension165 : FrameExtension frame165 :=
  matrix165.extension matrix165_dual frame165 (by decide) (by decide)

def matrix166 : MatrixWitness := ⟨![84#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,1#9,2#9,100#9,40#9,80#9,128#9,256#9]⟩
theorem matrix166_dual : matrix166.DualCheck := by decide
noncomputable def extension166 : FrameExtension frame166 :=
  matrix166.extension matrix166_dual frame166 (by decide) (by decide)

def matrix167 : MatrixWitness := ⟨![84#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,1#9,34#9,68#9,8#9,112#9,128#9,256#9]⟩
theorem matrix167_dual : matrix167.DualCheck := by decide
noncomputable def extension167 : FrameExtension frame167 :=
  matrix167.extension matrix167_dual frame167 (by decide) (by decide)

def matrix168 : MatrixWitness := ⟨![74#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,1#9,66#9,36#9,104#9,16#9,128#9,256#9]⟩
theorem matrix168_dual : matrix168.DualCheck := by decide
noncomputable def extension168 : FrameExtension frame168 :=
  matrix168.extension matrix168_dual frame168 (by decide) (by decide)

def matrix169 : MatrixWitness := ⟨![74#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,1#9,98#9,4#9,72#9,48#9,128#9,256#9]⟩
theorem matrix169_dual : matrix169.DualCheck := by decide
noncomputable def extension169 : FrameExtension frame169 :=
  matrix169.extension matrix169_dual frame169 (by decide) (by decide)

def matrix170 : MatrixWitness := ⟨![415#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,322#9,324#9,264#9,272#9,96#9,384#9]⟩
theorem matrix170_dual : matrix170.DualCheck := by decide
noncomputable def extension170 : FrameExtension frame170 :=
  matrix170.extension matrix170_dual frame170 (by decide) (by decide)

def matrix171 : MatrixWitness := ⟨![385#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,2#9,4#9,72#9,80#9,96#9,384#9]⟩
theorem matrix171_dual : matrix171.DualCheck := by decide
noncomputable def extension171 : FrameExtension frame171 :=
  matrix171.extension matrix171_dual frame171 (by decide) (by decide)

def matrix172 : MatrixWitness := ⟨![44#9,30#9,1#9,2#9,4#9,8#9,64#9,128#9,256#9], ![32#9,16#9,1#9,18#9,52#9,56#9,64#9,128#9,256#9]⟩
theorem matrix172_dual : matrix172.DualCheck := by decide
noncomputable def extension172 : FrameExtension frame172 :=
  matrix172.extension matrix172_dual frame172 (by decide) (by decide)

def matrix173 : MatrixWitness := ⟨![385#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,257#9,18#9,20#9,24#9,32#9,64#9,384#9]⟩
theorem matrix173_dual : matrix173.DualCheck := by decide
noncomputable def extension173 : FrameExtension frame173 :=
  matrix173.extension matrix173_dual frame173 (by decide) (by decide)

def matrix174 : MatrixWitness := ⟨![385#9,74#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,98#9,4#9,72#9,48#9,384#9]⟩
theorem matrix174_dual : matrix174.DualCheck := by decide
noncomputable def extension174 : FrameExtension frame174 :=
  matrix174.extension matrix174_dual frame174 (by decide) (by decide)

def matrix175 : MatrixWitness := ⟨![415#9,84#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,258#9,356#9,296#9,336#9,384#9]⟩
theorem matrix175_dual : matrix175.DualCheck := by decide
noncomputable def extension175 : FrameExtension frame175 :=
  matrix175.extension matrix175_dual frame175 (by decide) (by decide)

def matrix176 : MatrixWitness := ⟨![415#9,84#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,290#9,324#9,264#9,368#9,384#9]⟩
theorem matrix176_dual : matrix176.DualCheck := by decide
noncomputable def extension176 : FrameExtension frame176 :=
  matrix176.extension matrix176_dual frame176 (by decide) (by decide)

def matrix177 : MatrixWitness := ⟨![385#9,74#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,66#9,36#9,104#9,16#9,384#9]⟩
theorem matrix177_dual : matrix177.DualCheck := by decide
noncomputable def extension177 : FrameExtension frame177 :=
  matrix177.extension matrix177_dual frame177 (by decide) (by decide)

def matrix178 : MatrixWitness := ⟨![415#9,74#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,322#9,292#9,360#9,272#9,384#9]⟩
theorem matrix178_dual : matrix178.DualCheck := by decide
noncomputable def extension178 : FrameExtension frame178 :=
  matrix178.extension matrix178_dual frame178 (by decide) (by decide)

def matrix179 : MatrixWitness := ⟨![385#9,84#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,34#9,68#9,8#9,112#9,384#9]⟩
theorem matrix179_dual : matrix179.DualCheck := by decide
noncomputable def extension179 : FrameExtension frame179 :=
  matrix179.extension matrix179_dual frame179 (by decide) (by decide)

def matrix180 : MatrixWitness := ⟨![385#9,84#9,44#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,2#9,100#9,40#9,80#9,384#9]⟩
theorem matrix180_dual : matrix180.DualCheck := by decide
noncomputable def extension180 : FrameExtension frame180 :=
  matrix180.extension matrix180_dual frame180 (by decide) (by decide)

def matrix181 : MatrixWitness := ⟨![415#9,74#9,50#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,257#9,354#9,260#9,328#9,304#9,384#9]⟩
theorem matrix181_dual : matrix181.DualCheck := by decide
noncomputable def extension181 : FrameExtension frame181 :=
  matrix181.extension matrix181_dual frame181 (by decide) (by decide)

def matrix182 : MatrixWitness := ⟨![385#9,74#9,44#9,30#9,1#9,2#9,4#9,8#9,128#9], ![256#9,64#9,32#9,16#9,257#9,82#9,52#9,120#9,384#9]⟩
theorem matrix182_dual : matrix182.DualCheck := by decide
noncomputable def extension182 : FrameExtension frame182 :=
  matrix182.extension matrix182_dual frame182 (by decide) (by decide)

def matrix183 : MatrixWitness := ⟨![148#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,2#9,132#9,8#9,144#9,32#9,64#9,256#9]⟩
theorem matrix183_dual : matrix183.DualCheck := by decide
noncomputable def extension183 : FrameExtension frame183 :=
  matrix183.extension matrix183_dual frame183 (by decide) (by decide)

def matrix184 : MatrixWitness := ⟨![266#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,4#9,264#9,16#9,32#9,64#9,128#9]⟩
theorem matrix184_dual : matrix184.DualCheck := by decide
noncomputable def extension184 : FrameExtension frame184 :=
  matrix184.extension matrix184_dual frame184 (by decide) (by decide)

def matrix185 : MatrixWitness := ⟨![276#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,260#9,8#9,272#9,32#9,64#9,128#9]⟩
theorem matrix185_dual : matrix185.DualCheck := by decide
noncomputable def extension185 : FrameExtension frame185 :=
  matrix185.extension matrix185_dual frame185 (by decide) (by decide)

def matrix186 : MatrixWitness := ⟨![138#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,130#9,4#9,136#9,16#9,32#9,64#9,256#9]⟩
theorem matrix186_dual : matrix186.DualCheck := by decide
noncomputable def extension186 : FrameExtension frame186 :=
  matrix186.extension matrix186_dual frame186 (by decide) (by decide)

def matrix187 : MatrixWitness := ⟨![351#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,264#9,272#9,32#9,320#9,128#9]⟩
theorem matrix187_dual : matrix187.DualCheck := by decide
noncomputable def extension187 : FrameExtension frame187 :=
  matrix187.extension matrix187_dual frame187 (by decide) (by decide)

def matrix188 : MatrixWitness := ⟨![193#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,2#9,4#9,8#9,16#9,32#9,192#9,256#9]⟩
theorem matrix188_dual : matrix188.DualCheck := by decide
noncomputable def extension188 : FrameExtension frame188 :=
  matrix188.extension matrix188_dual frame188 (by decide) (by decide)

def matrix189 : MatrixWitness := ⟨![223#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,130#9,132#9,136#9,144#9,32#9,192#9,256#9]⟩
theorem matrix189_dual : matrix189.DualCheck := by decide
noncomputable def extension189 : FrameExtension frame189 :=
  matrix189.extension matrix189_dual frame189 (by decide) (by decide)

def matrix190 : MatrixWitness := ⟨![321#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,4#9,8#9,16#9,32#9,320#9,128#9]⟩
theorem matrix190_dual : matrix190.DualCheck := by decide
noncomputable def extension190 : FrameExtension frame190 :=
  matrix190.extension matrix190_dual frame190 (by decide) (by decide)

def matrix191 : MatrixWitness := ⟨![138#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,256#9], ![128#9,16#9,1#9,146#9,20#9,152#9,32#9,64#9,256#9]⟩
theorem matrix191_dual : matrix191.DualCheck := by decide
noncomputable def extension191 : FrameExtension frame191 :=
  matrix191.extension matrix191_dual frame191 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
