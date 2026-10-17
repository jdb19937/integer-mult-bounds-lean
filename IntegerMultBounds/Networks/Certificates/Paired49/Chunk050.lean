module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks
public import IntegerMultBounds.Networks.Certificates.Paired49.Chunk046

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk050_checked : checkChunk bank.lookup 6400 chunk050 = true := by
  decide +kernel

theorem chunk050_length : chunk050.length = 128 := by rfl

theorem chunk050_additions : chunk050.countP Entry.isAddition = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
