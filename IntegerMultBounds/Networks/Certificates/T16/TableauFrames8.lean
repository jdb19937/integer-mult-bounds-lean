module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix256 : MatrixWitness := ⟨![134#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,256#9], ![128#9,64#9,1#9,130#9,132#9,72#9,80#9,96#9,256#9]⟩
theorem matrix256_dual : matrix256.DualCheck := by decide
noncomputable def extension256 : FrameExtension frame256 :=
  matrix256.extension matrix256_dual frame256 (by decide) (by decide)

def matrix257 : MatrixWitness := ⟨![262#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,322#9,324#9,8#9,16#9,96#9,128#9]⟩
theorem matrix257_dual : matrix257.DualCheck := by decide
noncomputable def extension257 : FrameExtension frame257 :=
  matrix257.extension matrix257_dual frame257 (by decide) (by decide)

def matrix258 : MatrixWitness := ⟨![280#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,2#9,4#9,328#9,336#9,96#9,128#9]⟩
theorem matrix258_dual : matrix258.DualCheck := by decide
noncomputable def extension258 : FrameExtension frame258 :=
  matrix258.extension matrix258_dual frame258 (by decide) (by decide)

def matrix259 : MatrixWitness := ⟨![134#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,256#9], ![128#9,16#9,1#9,146#9,148#9,24#9,32#9,64#9,256#9]⟩
theorem matrix259_dual : matrix259.DualCheck := by decide
noncomputable def extension259 : FrameExtension frame259 :=
  matrix259.extension matrix259_dual frame259 (by decide) (by decide)

def matrix260 : MatrixWitness := ⟨![262#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,1#9,274#9,276#9,24#9,32#9,64#9,128#9]⟩
theorem matrix260_dual : matrix260.DualCheck := by decide
noncomputable def extension260 : FrameExtension frame260 :=
  matrix260.extension matrix260_dual frame260 (by decide) (by decide)

def matrix261 : MatrixWitness := ⟨![280#9,134#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,130#9,132#9,328#9,336#9,96#9]⟩
theorem matrix261_dual : matrix261.DualCheck := by decide
noncomputable def extension261 : FrameExtension frame261 :=
  matrix261.extension matrix261_dual frame261 (by decide) (by decide)

def matrix262 : MatrixWitness := ⟨![262#9,152#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,258#9,260#9,200#9,208#9,96#9]⟩
theorem matrix262_dual : matrix262.DualCheck := by decide
noncomputable def extension262 : FrameExtension frame262 :=
  matrix262.extension matrix262_dual frame262 (by decide) (by decide)

def matrix263 : MatrixWitness := ⟨![262#9,134#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,450#9,452#9,8#9,16#9,96#9]⟩
theorem matrix263_dual : matrix263.DualCheck := by decide
noncomputable def extension263 : FrameExtension frame263 :=
  matrix263.extension matrix263_dual frame263 (by decide) (by decide)

def matrix264 : MatrixWitness := ⟨![280#9,152#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,66#9,68#9,392#9,400#9,96#9]⟩
theorem matrix264_dual : matrix264.DualCheck := by decide
noncomputable def extension264 : FrameExtension frame264 :=
  matrix264.extension matrix264_dual frame264 (by decide) (by decide)

def matrix265 : MatrixWitness := ⟨![262#9,152#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,322#9,324#9,136#9,144#9,96#9]⟩
theorem matrix265_dual : matrix265.DualCheck := by decide
noncomputable def extension265 : FrameExtension frame265 :=
  matrix265.extension matrix265_dual frame265 (by decide) (by decide)

def matrix266 : MatrixWitness := ⟨![280#9,134#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,194#9,196#9,264#9,272#9,96#9]⟩
theorem matrix266_dual : matrix266.DualCheck := by decide
noncomputable def extension266 : FrameExtension frame266 :=
  matrix266.extension matrix266_dual frame266 (by decide) (by decide)

def matrix267 : MatrixWitness := ⟨![280#9,152#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,2#9,4#9,456#9,464#9,96#9]⟩
theorem matrix267_dual : matrix267.DualCheck := by decide
noncomputable def extension267 : FrameExtension frame267 :=
  matrix267.extension matrix267_dual frame267 (by decide) (by decide)

def matrix268 : MatrixWitness := ⟨![262#9,134#9,120#9,1#9,2#9,4#9,8#9,16#9,32#9], ![256#9,128#9,64#9,1#9,386#9,388#9,72#9,80#9,96#9]⟩
theorem matrix268_dual : matrix268.DualCheck := by decide
noncomputable def extension268 : FrameExtension frame268 :=
  matrix268.extension matrix268_dual frame268 (by decide) (by decide)

def matrix269 : MatrixWitness := ⟨![262#9,134#9,102#9,30#9,1#9,2#9,4#9,8#9,32#9], ![256#9,128#9,64#9,16#9,1#9,466#9,468#9,24#9,96#9]⟩
theorem matrix269_dual : matrix269.DualCheck := by decide
noncomputable def extension269 : FrameExtension frame269 :=
  matrix269.extension matrix269_dual frame269 (by decide) (by decide)

def matrix270 : MatrixWitness := ⟨![494#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,260#9,264#9,16#9,288#9,320#9,384#9]⟩
theorem matrix270_dual : matrix270.DualCheck := by decide
noncomputable def extension270 : FrameExtension frame270 :=
  matrix270.extension matrix270_dual frame270 (by decide) (by decide)

def matrix271 : MatrixWitness := ⟨![112#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,1#9,2#9,4#9,8#9,80#9,96#9,128#9,256#9]⟩
theorem matrix271_dual : matrix271.DualCheck := by decide
noncomputable def extension271 : FrameExtension frame271 :=
  matrix271.extension matrix271_dual frame271 (by decide) (by decide)

def matrix272 : MatrixWitness := ⟨![67#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9,256#9], ![64#9,65#9,66#9,4#9,8#9,16#9,32#9,128#9,256#9]⟩
theorem matrix272_dual : matrix272.DualCheck := by decide
noncomputable def extension272 : FrameExtension frame272 :=
  matrix272.extension matrix272_dual frame272 (by decide) (by decide)

def matrix273 : MatrixWitness := ⟨![477#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,260#9,264#9,272#9,32#9,320#9,384#9]⟩
theorem matrix273_dual : matrix273.DualCheck := by decide
noncomputable def extension273 : FrameExtension frame273 :=
  matrix273.extension matrix273_dual frame273 (by decide) (by decide)

def matrix274 : MatrixWitness := ⟨![37#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9,256#9], ![32#9,33#9,2#9,36#9,8#9,16#9,64#9,128#9,256#9]⟩
theorem matrix274_dual : matrix274.DualCheck := by decide
noncomputable def extension274 : FrameExtension frame274 :=
  matrix274.extension matrix274_dual frame274 (by decide) (by decide)

def matrix275 : MatrixWitness := ⟨![443#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,4#9,264#9,272#9,288#9,64#9,384#9]⟩
theorem matrix275_dual : matrix275.DualCheck := by decide
noncomputable def extension275 : FrameExtension frame275 :=
  matrix275.extension matrix275_dual frame275 (by decide) (by decide)

def matrix276 : MatrixWitness := ⟨![392#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,4#9,264#9,16#9,32#9,64#9,384#9]⟩
theorem matrix276_dual : matrix276.DualCheck := by decide
noncomputable def extension276 : FrameExtension frame276 :=
  matrix276.extension matrix276_dual frame276 (by decide) (by decide)

def matrix277 : MatrixWitness := ⟨![22#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9,256#9], ![16#9,1#9,18#9,20#9,8#9,32#9,64#9,128#9,256#9]⟩
theorem matrix277_dual : matrix277.DualCheck := by decide
noncomputable def extension277 : FrameExtension frame277 :=
  matrix277.extension matrix277_dual frame277 (by decide) (by decide)

def matrix278 : MatrixWitness := ⟨![477#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,289#9,34#9,260#9,264#9,304#9,320#9,384#9]⟩
theorem matrix278_dual : matrix278.DualCheck := by decide
noncomputable def extension278 : FrameExtension frame278 :=
  matrix278.extension matrix278_dual frame278 (by decide) (by decide)

def matrix279 : MatrixWitness := ⟨![443#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,321#9,258#9,68#9,264#9,336#9,288#9,384#9]⟩
theorem matrix279_dual : matrix279.DualCheck := by decide
noncomputable def extension279 : FrameExtension frame279 :=
  matrix279.extension matrix279_dual frame279 (by decide) (by decide)

def matrix280 : MatrixWitness := ⟨![392#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,1#9,66#9,68#9,264#9,16#9,96#9,384#9]⟩
theorem matrix280_dual : matrix280.DualCheck := by decide
noncomputable def extension280 : FrameExtension frame280 :=
  matrix280.extension matrix280_dual frame280 (by decide) (by decide)

def matrix281 : MatrixWitness := ⟨![67#9,51#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,98#9,4#9,8#9,48#9,128#9,256#9]⟩
theorem matrix281_dual : matrix281.DualCheck := by decide
noncomputable def extension281 : FrameExtension frame281 :=
  matrix281.extension matrix281_dual frame281 (by decide) (by decide)

def matrix282 : MatrixWitness := ⟨![85#9,37#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,2#9,100#9,8#9,80#9,128#9,256#9]⟩
theorem matrix282_dual : matrix282.DualCheck := by decide
noncomputable def extension282 : FrameExtension frame282 :=
  matrix282.extension matrix282_dual frame282 (by decide) (by decide)

def matrix283 : MatrixWitness := ⟨![102#9,22#9,1#9,2#9,4#9,8#9,32#9,128#9,256#9], ![64#9,16#9,1#9,82#9,84#9,8#9,96#9,128#9,256#9]⟩
theorem matrix283_dual : matrix283.DualCheck := by decide
noncomputable def extension283 : FrameExtension frame283 :=
  matrix283.extension matrix283_dual frame283 (by decide) (by decide)

def matrix284 : MatrixWitness := ⟨![67#9,37#9,1#9,2#9,4#9,8#9,16#9,128#9,256#9], ![64#9,32#9,97#9,66#9,36#9,8#9,16#9,128#9,256#9]⟩
theorem matrix284_dual : matrix284.DualCheck := by decide
noncomputable def extension284 : FrameExtension frame284 :=
  matrix284.extension matrix284_dual frame284 (by decide) (by decide)

def matrix285 : MatrixWitness := ⟨![67#9,22#9,1#9,2#9,4#9,8#9,32#9,128#9,256#9], ![64#9,16#9,65#9,82#9,20#9,8#9,32#9,128#9,256#9]⟩
theorem matrix285_dual : matrix285.DualCheck := by decide
noncomputable def extension285 : FrameExtension frame285 :=
  matrix285.extension matrix285_dual frame285 (by decide) (by decide)

def matrix286 : MatrixWitness := ⟨![443#9,102#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,257#9,322#9,68#9,264#9,272#9,352#9,384#9]⟩
theorem matrix286_dual : matrix286.DualCheck := by decide
noncomputable def extension286 : FrameExtension frame286 :=
  matrix286.extension matrix286_dual frame286 (by decide) (by decide)

def matrix287 : MatrixWitness := ⟨![392#9,85#9,1#9,2#9,4#9,8#9,16#9,32#9,128#9], ![256#9,64#9,65#9,2#9,68#9,264#9,80#9,32#9,384#9]⟩
theorem matrix287_dual : matrix287.DualCheck := by decide
noncomputable def extension287 : FrameExtension frame287 :=
  matrix287.extension matrix287_dual frame287 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
