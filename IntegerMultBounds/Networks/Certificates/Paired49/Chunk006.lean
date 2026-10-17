module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks
public import IntegerMultBounds.Networks.Certificates.Paired49.Chunk002

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk006_checked : checkChunk bank.lookup 768 chunk006 = true := by
  decide +kernel

theorem chunk006_length : chunk006.length = 128 := by rfl

theorem chunk006_additions : chunk006.countP Entry.isAddition = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
