module

public import IntegerMultBounds.Networks.Certificates.Paired49.Data
public import IntegerMultBounds.Networks.MaskDAGChunks
public import IntegerMultBounds.Networks.Certificates.Paired49.Chunk004

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk008_checked : checkChunk bank.lookup 1024 chunk008 = true := by
  decide +kernel

theorem chunk008_length : chunk008.length = 128 := by rfl

theorem chunk008_additions : chunk008.countP Entry.isAddition = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
