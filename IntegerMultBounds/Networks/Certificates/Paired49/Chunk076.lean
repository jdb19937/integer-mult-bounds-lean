module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks
public import IntegerMultBounds.Networks.Certificates.Paired49.Chunk072

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk076_checked : checkChunk bank.lookup 9728 chunk076 = true := by
  decide +kernel

theorem chunk076_length : chunk076.length = 128 := by rfl

theorem chunk076_additions : chunk076.countP Entry.isAddition = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
