module

public import IntegerMultBounds.Networks.Certificates.T16.TableauFramesModel

/-! Generated from pinned source data and the exact greedy extension rule. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def matrix512 : MatrixWitness := ⟨![256#9,128#9,89#9,40#9,5#9,2#9,1#9,8#9,16#9], ![256#9,128#9,64#9,32#9,4#9,2#9,69#9,104#9,80#9]⟩
theorem matrix512_dual : matrix512.DualCheck := by decide
noncomputable def extension512 : FrameExtension frame512 :=
  matrix512.extension matrix512_dual frame512 (by decide) (by decide)

def matrix513 : MatrixWitness := ⟨![256#9,128#9,64#9,40#9,25#9,5#9,2#9,1#9,8#9], ![256#9,128#9,64#9,32#9,16#9,4#9,2#9,21#9,56#9]⟩
theorem matrix513_dual : matrix513.DualCheck := by decide
noncomputable def extension513 : FrameExtension frame513 :=
  matrix513.extension matrix513_dual frame513 (by decide) (by decide)

def matrix514 : MatrixWitness := ⟨![256#9,137#9,64#9,40#9,16#9,5#9,2#9,1#9,8#9], ![256#9,128#9,64#9,32#9,16#9,4#9,2#9,133#9,168#9]⟩
theorem matrix514_dual : matrix514.DualCheck := by decide
noncomputable def extension514 : FrameExtension frame514 :=
  matrix514.extension matrix514_dual frame514 (by decide) (by decide)

def matrix515 : MatrixWitness := ⟨![448#9,45#9,21#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,49#9,2#9,52#9,40#9,320#9,384#9]⟩
theorem matrix515_dual : matrix515.DualCheck := by decide
noncomputable def extension515 : FrameExtension frame515 :=
  matrix515.extension matrix515_dual frame515 (by decide) (by decide)

def matrix516 : MatrixWitness := ⟨![194#9,45#9,28#9,1#9,2#9,4#9,8#9,64#9,256#9], ![128#9,32#9,16#9,33#9,130#9,52#9,56#9,192#9,256#9]⟩
theorem matrix516_dual : matrix516.DualCheck := by decide
noncomputable def extension516 : FrameExtension frame516 :=
  matrix516.extension matrix516_dual frame516 (by decide) (by decide)

def matrix517 : MatrixWitness := ⟨![322#9,192#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,258#9,36#9,40#9,16#9,448#9]⟩
theorem matrix517_dual : matrix517.DualCheck := by decide
noncomputable def extension517 : FrameExtension frame517 :=
  matrix517.extension matrix517_dual frame517 (by decide) (by decide)

def matrix518 : MatrixWitness := ⟨![258#9,194#9,45#9,28#9,1#9,2#9,4#9,8#9,64#9], ![256#9,128#9,32#9,16#9,33#9,386#9,52#9,56#9,192#9]⟩
theorem matrix518_dual : matrix518.DualCheck := by decide
noncomputable def extension518 : FrameExtension frame518 :=
  matrix518.extension matrix518_dual frame518 (by decide) (by decide)

def matrix519 : MatrixWitness := ⟨![386#9,66#9,45#9,21#9,1#9,2#9,4#9,8#9,128#9], ![256#9,64#9,32#9,16#9,49#9,322#9,52#9,40#9,384#9]⟩
theorem matrix519_dual : matrix519.DualCheck := by decide
noncomputable def extension519 : FrameExtension frame519 :=
  matrix519.extension matrix519_dual frame519 (by decide) (by decide)

def matrix520 : MatrixWitness := ⟨![320#9,192#9,45#9,2#9,1#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,2#9,33#9,36#9,40#9,16#9,448#9]⟩
theorem matrix520_dual : matrix520.DualCheck := by decide
noncomputable def extension520 : FrameExtension frame520 :=
  matrix520.extension matrix520_dual frame520 (by decide) (by decide)

def matrix521 : MatrixWitness := ⟨![320#9,192#9,33#9,21#9,12#9,2#9,1#9,4#9,64#9], ![256#9,128#9,32#9,16#9,8#9,2#9,49#9,28#9,448#9]⟩
theorem matrix521_dual : matrix521.DualCheck := by decide
noncomputable def extension521 : FrameExtension frame521 :=
  matrix521.extension matrix521_dual frame521 (by decide) (by decide)

def matrix522 : MatrixWitness := ⟨![386#9,66#9,33#9,16#9,9#9,5#9,1#9,2#9,128#9], ![256#9,64#9,32#9,16#9,8#9,4#9,45#9,322#9,384#9]⟩
theorem matrix522_dual : matrix522.DualCheck := by decide
noncomputable def extension522 : FrameExtension frame522 :=
  matrix522.extension matrix522_dual frame522 (by decide) (by decide)

def matrix523 : MatrixWitness := ⟨![258#9,130#9,64#9,40#9,25#9,5#9,1#9,2#9,8#9], ![256#9,128#9,64#9,32#9,16#9,4#9,21#9,386#9,56#9]⟩
theorem matrix523_dual : matrix523.DualCheck := by decide
noncomputable def extension523 : FrameExtension frame523 :=
  matrix523.extension matrix523_dual frame523 (by decide) (by decide)

def matrix524 : MatrixWitness := ⟨![258#9,128#9,66#9,33#9,16#9,9#9,5#9,1#9,2#9], ![256#9,128#9,64#9,32#9,16#9,8#9,4#9,45#9,322#9]⟩
theorem matrix524_dual : matrix524.DualCheck := by decide
noncomputable def extension524 : FrameExtension frame524 :=
  matrix524.extension matrix524_dual frame524 (by decide) (by decide)

def matrix525 : MatrixWitness := ⟨![336#9,133#9,45#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,161#9,2#9,164#9,40#9,272#9,320#9]⟩
theorem matrix525_dual : matrix525.DualCheck := by decide
noncomputable def extension525 : FrameExtension frame525 :=
  matrix525.extension matrix525_dual frame525 (by decide) (by decide)

def matrix526 : MatrixWitness := ⟨![137#9,40#9,5#9,1#9,2#9,8#9,16#9,64#9,256#9], ![128#9,32#9,4#9,133#9,2#9,168#9,16#9,64#9,256#9]⟩
theorem matrix526_dual : matrix526.DualCheck := by decide
noncomputable def extension526 : FrameExtension frame526 :=
  matrix526.extension matrix526_dual frame526 (by decide) (by decide)

def matrix527 : MatrixWitness := ⟨![274#9,80#9,45#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,33#9,258#9,36#9,40#9,336#9,128#9]⟩
theorem matrix527_dual : matrix527.DualCheck := by decide
noncomputable def extension527 : FrameExtension frame527 :=
  matrix527.extension matrix527_dual frame527 (by decide) (by decide)

def matrix528 : MatrixWitness := ⟨![336#9,137#9,40#9,5#9,1#9,2#9,8#9,16#9,64#9], ![256#9,128#9,32#9,4#9,133#9,2#9,168#9,272#9,320#9]⟩
theorem matrix528_dual : matrix528.DualCheck := by decide
noncomputable def extension528 : FrameExtension frame528 :=
  matrix528.extension matrix528_dual frame528 (by decide) (by decide)

def matrix529 : MatrixWitness := ⟨![274#9,133#9,66#9,45#9,1#9,2#9,4#9,8#9,16#9], ![256#9,128#9,64#9,32#9,161#9,322#9,164#9,40#9,272#9]⟩
theorem matrix529_dual : matrix529.DualCheck := by decide
noncomputable def extension529 : FrameExtension frame529 :=
  matrix529.extension matrix529_dual frame529 (by decide) (by decide)

def matrix530 : MatrixWitness := ⟨![274#9,137#9,80#9,45#9,1#9,2#9,4#9,8#9,16#9], ![256#9,128#9,64#9,32#9,161#9,258#9,36#9,168#9,336#9]⟩
theorem matrix530_dual : matrix530.DualCheck := by decide
noncomputable def extension530 : FrameExtension frame530 :=
  matrix530.extension matrix530_dual frame530 (by decide) (by decide)

def matrix531 : MatrixWitness := ⟨![272#9,133#9,80#9,33#9,12#9,2#9,1#9,4#9,16#9], ![256#9,128#9,64#9,32#9,8#9,2#9,161#9,140#9,336#9]⟩
theorem matrix531_dual : matrix531.DualCheck := by decide
noncomputable def extension531 : FrameExtension frame531 :=
  matrix531.extension matrix531_dual frame531 (by decide) (by decide)

def matrix532 : MatrixWitness := ⟨![258#9,133#9,66#9,36#9,16#9,9#9,1#9,2#9,4#9], ![256#9,128#9,64#9,32#9,16#9,8#9,137#9,322#9,164#9]⟩
theorem matrix532_dual : matrix532.DualCheck := by decide
noncomputable def extension532 : FrameExtension frame532 :=
  matrix532.extension matrix532_dual frame532 (by decide) (by decide)

def matrix533 : MatrixWitness := ⟨![258#9,137#9,64#9,40#9,18#9,5#9,1#9,2#9,8#9], ![256#9,128#9,64#9,32#9,16#9,4#9,133#9,274#9,168#9]⟩
theorem matrix533_dual : matrix533.DualCheck := by decide
noncomputable def extension533 : FrameExtension frame533 :=
  matrix533.extension matrix533_dual frame533 (by decide) (by decide)

def matrix534 : MatrixWitness := ⟨![414#9,81#9,51#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,290#9,260#9,264#9,368#9,384#9]⟩
theorem matrix534_dual : matrix534.DualCheck := by decide
noncomputable def extension534 : FrameExtension frame534 :=
  matrix534.extension matrix534_dual frame534 (by decide) (by decide)

def matrix535 : MatrixWitness := ⟨![388#9,41#9,26#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,33#9,18#9,260#9,56#9,64#9,384#9]⟩
theorem matrix535_dual : matrix535.DualCheck := by decide
noncomputable def extension535 : FrameExtension frame535 :=
  matrix535.extension matrix535_dual frame535 (by decide) (by decide)

def matrix536 : MatrixWitness := ⟨![388#9,81#9,51#9,1#9,2#9,4#9,8#9,16#9,128#9], ![256#9,64#9,32#9,97#9,34#9,260#9,8#9,112#9,384#9]⟩
theorem matrix536_dual : matrix536.DualCheck := by decide
noncomputable def extension536 : FrameExtension frame536 :=
  matrix536.extension matrix536_dual frame536 (by decide) (by decide)

def matrix537 : MatrixWitness := ⟨![463#9,41#9,26#9,1#9,2#9,4#9,8#9,64#9,128#9], ![256#9,32#9,16#9,289#9,274#9,260#9,312#9,320#9,384#9]⟩
theorem matrix537_dual : matrix537.DualCheck := by decide
noncomputable def extension537 : FrameExtension frame537 :=
  matrix537.extension matrix537_dual frame537 (by decide) (by decide)

def matrix538 : MatrixWitness := ⟨![387#9,64#9,34#9,17#9,8#9,4#9,1#9,2#9,128#9], ![256#9,64#9,32#9,16#9,8#9,4#9,273#9,290#9,384#9]⟩
theorem matrix538_dual : matrix538.DualCheck := by decide
noncomputable def extension538 : FrameExtension frame538 :=
  matrix538.extension matrix538_dual frame538 (by decide) (by decide)

def matrix539 : MatrixWitness := ⟨![388#9,68#9,33#9,17#9,8#9,3#9,1#9,4#9,128#9], ![256#9,64#9,32#9,16#9,8#9,2#9,51#9,324#9,384#9]⟩
theorem matrix539_dual : matrix539.DualCheck := by decide
noncomputable def extension539 : FrameExtension frame539 :=
  matrix539.extension matrix539_dual frame539 (by decide) (by decide)

def matrix540 : MatrixWitness := ⟨![273#9,145#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,417#9,34#9,4#9,8#9,432#9,64#9]⟩
theorem matrix540_dual : matrix540.DualCheck := by decide
noncomputable def extension540 : FrameExtension frame540 :=
  matrix540.extension matrix540_dual frame540 (by decide) (by decide)

def matrix541 : MatrixWitness := ⟨![324#9,196#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,33#9,34#9,388#9,8#9,48#9,448#9]⟩
theorem matrix541_dual : matrix541.DualCheck := by decide
noncomputable def extension541 : FrameExtension frame541 :=
  matrix541.extension matrix541_dual frame541 (by decide) (by decide)

def matrix542 : MatrixWitness := ⟨![273#9,196#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,289#9,34#9,132#9,8#9,304#9,192#9]⟩
theorem matrix542_dual : matrix542.DualCheck := by decide
noncomputable def extension542 : FrameExtension frame542 :=
  matrix542.extension matrix542_dual frame542 (by decide) (by decide)

def matrix543 : MatrixWitness := ⟨![324#9,145#9,51#9,1#9,2#9,4#9,8#9,16#9,64#9], ![256#9,128#9,32#9,161#9,34#9,260#9,8#9,176#9,320#9]⟩
theorem matrix543_dual : matrix543.DualCheck := by decide
noncomputable def extension543 : FrameExtension frame543 :=
  matrix543.extension matrix543_dual frame543 (by decide) (by decide)


end IntegerMultBounds.Networks.Certificates.T16.Tableau
