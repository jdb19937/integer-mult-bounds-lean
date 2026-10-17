module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks
public import IntegerMultBounds.Networks.Certificates.Paired49.Chunk078

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk082_checked : checkChunk bank.lookup 10496 chunk082 = true := by
  decide +kernel

theorem chunk082_length : chunk082.length = 128 := by rfl

theorem chunk082_additions : chunk082.countP Entry.isAddition = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
