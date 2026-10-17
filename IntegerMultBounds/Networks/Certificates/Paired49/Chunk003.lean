module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk003_checked : checkChunk bank.lookup 384 chunk003 = true := by
  decide +kernel

theorem chunk003_length : chunk003.length = 128 := by rfl

theorem chunk003_additions : chunk003.countP Entry.isAddition = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
