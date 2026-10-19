module

public import IntegerMultBounds.Networks.GaussianBoundedArithmetic
public import IntegerMultBounds.Networks.BinaryColumnFrame

/-! Every actual binary phase frame has an explicit grid bound, without a
residual-factor certificate or nondegeneracy premise. This applies to the
role-specific frames retained by the actual grouped network compiler. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GaussianPrecision
open BinaryWalsh

end IntegerMultBounds.Networks.GaussianPrecision
