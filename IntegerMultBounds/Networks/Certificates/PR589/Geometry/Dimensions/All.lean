module

public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block000
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block001
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block002
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block003
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block004
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block005
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block006
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block007
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block008
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block009
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block010
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block011
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block012
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block013
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block014
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block015
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block016
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block017
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block018
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block019
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block020
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block021
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block022
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block023
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block024
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block025
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block026
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block027
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block028
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block029
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block030
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block031
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block032
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block033
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block034
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block035
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block036
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block037
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block038
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Block039

/-! Generated exact rational witnesses; all equations are kernel checked. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions

/-- Every literal PR589 label has its actual rational root-span dimension. -/
theorem dimension (i : ℕ) (hi : i < 636) : Module.finrank ℚ (label i) = value i := by
  by_cases h20 : i < 320
  ·
    by_cases h10 : i < 160
    ·
      by_cases h5 : i < 80
      ·
        by_cases h2 : i < 32
        ·
          by_cases h1 : i < 16
          ·
            exact block000 i (by omega) (by omega)
          ·
            exact block001 i (by omega) (by omega)
        ·
          by_cases h3 : i < 48
          ·
            exact block002 i (by omega) (by omega)
          ·
            by_cases h4 : i < 64
            ·
              exact block003 i (by omega) (by omega)
            ·
              exact block004 i (by omega) (by omega)
      ·
        by_cases h7 : i < 112
        ·
          by_cases h6 : i < 96
          ·
            exact block005 i (by omega) (by omega)
          ·
            exact block006 i (by omega) (by omega)
        ·
          by_cases h8 : i < 128
          ·
            exact block007 i (by omega) (by omega)
          ·
            by_cases h9 : i < 144
            ·
              exact block008 i (by omega) (by omega)
            ·
              exact block009 i (by omega) (by omega)
    ·
      by_cases h15 : i < 240
      ·
        by_cases h12 : i < 192
        ·
          by_cases h11 : i < 176
          ·
            exact block010 i (by omega) (by omega)
          ·
            exact block011 i (by omega) (by omega)
        ·
          by_cases h13 : i < 208
          ·
            exact block012 i (by omega) (by omega)
          ·
            by_cases h14 : i < 224
            ·
              exact block013 i (by omega) (by omega)
            ·
              exact block014 i (by omega) (by omega)
      ·
        by_cases h17 : i < 272
        ·
          by_cases h16 : i < 256
          ·
            exact block015 i (by omega) (by omega)
          ·
            exact block016 i (by omega) (by omega)
        ·
          by_cases h18 : i < 288
          ·
            exact block017 i (by omega) (by omega)
          ·
            by_cases h19 : i < 304
            ·
              exact block018 i (by omega) (by omega)
            ·
              exact block019 i (by omega) (by omega)
  ·
    by_cases h30 : i < 480
    ·
      by_cases h25 : i < 400
      ·
        by_cases h22 : i < 352
        ·
          by_cases h21 : i < 336
          ·
            exact block020 i (by omega) (by omega)
          ·
            exact block021 i (by omega) (by omega)
        ·
          by_cases h23 : i < 368
          ·
            exact block022 i (by omega) (by omega)
          ·
            by_cases h24 : i < 384
            ·
              exact block023 i (by omega) (by omega)
            ·
              exact block024 i (by omega) (by omega)
      ·
        by_cases h27 : i < 432
        ·
          by_cases h26 : i < 416
          ·
            exact block025 i (by omega) (by omega)
          ·
            exact block026 i (by omega) (by omega)
        ·
          by_cases h28 : i < 448
          ·
            exact block027 i (by omega) (by omega)
          ·
            by_cases h29 : i < 464
            ·
              exact block028 i (by omega) (by omega)
            ·
              exact block029 i (by omega) (by omega)
    ·
      by_cases h35 : i < 560
      ·
        by_cases h32 : i < 512
        ·
          by_cases h31 : i < 496
          ·
            exact block030 i (by omega) (by omega)
          ·
            exact block031 i (by omega) (by omega)
        ·
          by_cases h33 : i < 528
          ·
            exact block032 i (by omega) (by omega)
          ·
            by_cases h34 : i < 544
            ·
              exact block033 i (by omega) (by omega)
            ·
              exact block034 i (by omega) (by omega)
      ·
        by_cases h37 : i < 592
        ·
          by_cases h36 : i < 576
          ·
            exact block035 i (by omega) (by omega)
          ·
            exact block036 i (by omega) (by omega)
        ·
          by_cases h38 : i < 608
          ·
            exact block037 i (by omega) (by omega)
          ·
            by_cases h39 : i < 624
            ·
              exact block038 i (by omega) (by omega)
            ·
              exact block039 i (by omega) (by omega)

end IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions
