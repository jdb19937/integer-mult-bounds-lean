module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix384 : MatrixWitness := ⟨![414#9,73#9,49#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,258#9,260#9,328#9,304#9,384#9]⟩
theorem matrix384_dual : matrix384.DualCheck := by decide
noncomputable def extension384 : FrameExtension frame384 :=
  matrix384.extension matrix384_dual frame384 (by decide) (by decide)

def matrix385 : MatrixWitness := ⟨![386#9,73#9,45#9,28#9,1#9,2#9,4#9,8#9,128#9], ![256#9,64#9,32#9,16#9,97#9,258#9,52#9,120#9,384#9]⟩
theorem matrix385_dual : matrix385.DualCheck := by decide
noncomputable def extension385 : FrameExtension frame385 :=
  matrix385.extension matrix385_dual frame385 (by decide) (by decide)

def matrix386 : MatrixWitness := ⟨![146#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,130#9,4#9,8#9,144#9,32#9,64#9,256#9]⟩
theorem matrix386_dual : matrix386.DualCheck := by decide
noncomputable def extension386 : FrameExtension frame386 :=
  matrix386.extension matrix386_dual frame386 (by decide) (by decide)

def matrix387 : MatrixWitness := ⟨![289#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,2#9,4#9,8#9,16#9,288#9,64#9,128#9]⟩
theorem matrix387_dual : matrix387.DualCheck := by decide
noncomputable def extension387 : FrameExtension frame387 :=
  matrix387.extension matrix387_dual frame387 (by decide) (by decide)

def matrix388 : MatrixWitness := ⟨![268#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,2#9,260#9,264#9,16#9,32#9,64#9,128#9]⟩
theorem matrix388_dual : matrix388.DualCheck := by decide
noncomputable def extension388 : FrameExtension frame388 :=
  matrix388.extension matrix388_dual frame388 (by decide) (by decide)

def matrix389 : MatrixWitness := ⟨![191#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,130#9,132#9,136#9,144#9,160#9,64#9,256#9]⟩
theorem matrix389_dual : matrix389.DualCheck := by decide
noncomputable def extension389 : FrameExtension frame389 :=
  matrix389.extension matrix389_dual frame389 (by decide) (by decide)

def matrix390 : MatrixWitness := ⟨![274#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,1#9,258#9,4#9,8#9,272#9,32#9,64#9,128#9]⟩
theorem matrix390_dual : matrix390.DualCheck := by decide
noncomputable def extension390 : FrameExtension frame390 :=
  matrix390.extension matrix390_dual frame390 (by decide) (by decide)

def matrix391 : MatrixWitness := ⟨![161#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,129#9,2#9,4#9,8#9,16#9,160#9,64#9,256#9]⟩
theorem matrix391_dual : matrix391.DualCheck := by decide
noncomputable def extension391 : FrameExtension frame391 :=
  matrix391.extension matrix391_dual frame391 (by decide) (by decide)

def matrix392 : MatrixWitness := ⟨![140#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,256#9], ![128#9,1#9,2#9,132#9,136#9,16#9,32#9,64#9,256#9]⟩
theorem matrix392_dual : matrix392.DualCheck := by decide
noncomputable def extension392 : FrameExtension frame392 :=
  matrix392.extension matrix392_dual frame392 (by decide) (by decide)

def matrix393 : MatrixWitness := ⟨![319#9,1#9,2#9,4#9,8#9,16#9,32#9,64#9,128#9], ![256#9,257#9,258#9,260#9,264#9,272#9,288#9,64#9,128#9]⟩
theorem matrix393_dual : matrix393.DualCheck := by decide
noncomputable def extension393 : FrameExtension frame393 :=
  matrix393.extension matrix393_dual frame393 (by decide) (by decide)

def matrix394 : MatrixWitness := ⟨![146#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,130#9,36#9,40#9,144#9,64#9,256#9]⟩
theorem matrix394_dual : matrix394.DualCheck := by decide
noncomputable def extension394 : FrameExtension frame394 :=
  matrix394.extension matrix394_dual frame394 (by decide) (by decide)

def matrix395 : MatrixWitness := ⟨![146#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,162#9,4#9,8#9,176#9,64#9,256#9]⟩
theorem matrix395_dual : matrix395.DualCheck := by decide
noncomputable def extension395 : FrameExtension frame395 :=
  matrix395.extension matrix395_dual frame395 (by decide) (by decide)

def matrix396 : MatrixWitness := ⟨![140#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,256#9], ![128#9,16#9,1#9,18#9,148#9,152#9,32#9,64#9,256#9]⟩
theorem matrix396_dual : matrix396.DualCheck := by decide
noncomputable def extension396 : FrameExtension frame396 :=
  matrix396.extension matrix396_dual frame396 (by decide) (by decide)

def matrix397 : MatrixWitness := ⟨![268#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,2#9,292#9,296#9,16#9,64#9,128#9]⟩
theorem matrix397_dual : matrix397.DualCheck := by decide
noncomputable def extension397 : FrameExtension frame397 :=
  matrix397.extension matrix397_dual frame397 (by decide) (by decide)

def matrix398 : MatrixWitness := ⟨![274#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,290#9,4#9,8#9,304#9,64#9,128#9]⟩
theorem matrix398_dual : matrix398.DualCheck := by decide
noncomputable def extension398 : FrameExtension frame398 :=
  matrix398.extension matrix398_dual frame398 (by decide) (by decide)

def matrix399 : MatrixWitness := ⟨![289#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,257#9,18#9,20#9,24#9,288#9,64#9,128#9]⟩
theorem matrix399_dual : matrix399.DualCheck := by decide
noncomputable def extension399 : FrameExtension frame399 :=
  matrix399.extension matrix399_dual frame399 (by decide) (by decide)

def matrix400 : MatrixWitness := ⟨![268#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,128#9], ![256#9,16#9,1#9,18#9,276#9,280#9,32#9,64#9,128#9]⟩
theorem matrix400_dual : matrix400.DualCheck := by decide
noncomputable def extension400 : FrameExtension frame400 :=
  matrix400.extension matrix400_dual frame400 (by decide) (by decide)

def matrix401 : MatrixWitness := ⟨![268#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,34#9,260#9,264#9,48#9,64#9,128#9]⟩
theorem matrix401_dual : matrix401.DualCheck := by decide
noncomputable def extension401 : FrameExtension frame401 :=
  matrix401.extension matrix401_dual frame401 (by decide) (by decide)

def matrix402 : MatrixWitness := ⟨![161#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9,256#9], ![128#9,16#9,129#9,18#9,20#9,24#9,160#9,64#9,256#9]⟩
theorem matrix402_dual : matrix402.DualCheck := by decide
noncomputable def extension402 : FrameExtension frame402 :=
  matrix402.extension matrix402_dual frame402 (by decide) (by decide)

def matrix403 : MatrixWitness := ⟨![140#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,34#9,132#9,136#9,48#9,64#9,256#9]⟩
theorem matrix403_dual : matrix403.DualCheck := by decide
noncomputable def extension403 : FrameExtension frame403 :=
  matrix403.extension matrix403_dual frame403 (by decide) (by decide)

def matrix404 : MatrixWitness := ⟨![274#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,128#9], ![256#9,32#9,33#9,258#9,36#9,40#9,272#9,64#9,128#9]⟩
theorem matrix404_dual : matrix404.DualCheck := by decide
noncomputable def extension404 : FrameExtension frame404 :=
  matrix404.extension matrix404_dual frame404 (by decide) (by decide)

def matrix405 : MatrixWitness := ⟨![140#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9,256#9], ![128#9,32#9,33#9,2#9,164#9,168#9,16#9,64#9,256#9]⟩
theorem matrix405_dual : matrix405.DualCheck := by decide
noncomputable def extension405 : FrameExtension frame405 :=
  matrix405.extension matrix405_dual frame405 (by decide) (by decide)

def matrix406 : MatrixWitness := ⟨![268#9,140#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,34#9,388#9,392#9,48#9,64#9]⟩
theorem matrix406_dual : matrix406.DualCheck := by decide
noncomputable def extension406 : FrameExtension frame406 :=
  matrix406.extension matrix406_dual frame406 (by decide) (by decide)

def matrix407 : MatrixWitness := ⟨![274#9,146#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,418#9,4#9,8#9,432#9,64#9]⟩
theorem matrix407_dual : matrix407.DualCheck := by decide
noncomputable def extension407 : FrameExtension frame407 :=
  matrix407.extension matrix407_dual frame407 (by decide) (by decide)

def matrix408 : MatrixWitness := ⟨![289#9,161#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9], ![256#9,128#9,16#9,385#9,18#9,20#9,24#9,416#9,64#9]⟩
theorem matrix408_dual : matrix408.DualCheck := by decide
noncomputable def extension408 : FrameExtension frame408 :=
  matrix408.extension matrix408_dual frame408 (by decide) (by decide)

def matrix409 : MatrixWitness := ⟨![268#9,140#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9], ![256#9,128#9,16#9,1#9,18#9,404#9,408#9,32#9,64#9]⟩
theorem matrix409_dual : matrix409.DualCheck := by decide
noncomputable def extension409 : FrameExtension frame409 :=
  matrix409.extension matrix409_dual frame409 (by decide) (by decide)

def matrix410 : MatrixWitness := ⟨![268#9,161#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9], ![256#9,128#9,16#9,129#9,18#9,276#9,280#9,160#9,64#9]⟩
theorem matrix410_dual : matrix410.DualCheck := by decide
noncomputable def extension410 : FrameExtension frame410 :=
  matrix410.extension matrix410_dual frame410 (by decide) (by decide)

def matrix411 : MatrixWitness := ⟨![289#9,140#9,30#9,1#9,2#9,4#9,8#9,32#9,64#9], ![256#9,128#9,16#9,257#9,18#9,148#9,152#9,288#9,64#9]⟩
theorem matrix411_dual : matrix411.DualCheck := by decide
noncomputable def extension411 : FrameExtension frame411 :=
  matrix411.extension matrix411_dual frame411 (by decide) (by decide)

def matrix412 : MatrixWitness := ⟨![274#9,140#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,290#9,132#9,136#9,304#9,64#9]⟩
theorem matrix412_dual : matrix412.DualCheck := by decide
noncomputable def extension412 : FrameExtension frame412 :=
  matrix412.extension matrix412_dual frame412 (by decide) (by decide)

def matrix413 : MatrixWitness := ⟨![268#9,146#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,162#9,260#9,264#9,176#9,64#9]⟩
theorem matrix413_dual : matrix413.DualCheck := by decide
noncomputable def extension413 : FrameExtension frame413 :=
  matrix413.extension matrix413_dual frame413 (by decide) (by decide)

def matrix414 : MatrixWitness := ⟨![268#9,140#9,45#9,30#9,1#9,2#9,4#9,8#9,64#9], ![256#9,128#9,32#9,16#9,33#9,18#9,436#9,440#9,64#9]⟩
theorem matrix414_dual : matrix414.DualCheck := by decide
noncomputable def extension414 : FrameExtension frame414 :=
  matrix414.extension matrix414_dual frame414 (by decide) (by decide)

def matrix415 : MatrixWitness := ⟨![256#9,128#9,64#9,34#9,16#9,10#9,4#9,1#9,2#9], ![256#9,128#9,64#9,32#9,16#9,8#9,4#9,1#9,42#9]⟩
theorem matrix415_dual : matrix415.DualCheck := by decide
noncomputable def extension415 : FrameExtension frame415 :=
  matrix415.extension matrix415_dual frame415 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
