module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2336 : Fin frame708.rank → ℕ := ![33,34,20,24,64,128]
theorem edge2336_span : frame708.space ≤ frame1002.space :=
  frame708.inclusion frame1002 witness2336 (by decide)
def edge2336 : CertifiedEdge catalog where
  old := 708
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2336_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2337 : Fin frame709.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2337_span : frame709.space ≤ frame921.space :=
  frame709.inclusion frame921 witness2337 (by decide)
def edge2337 : CertifiedEdge catalog where
  old := 709
  next := 921
  rank := 1
  good := by
    constructor
    · exact edge2337_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2338 : Fin frame709.rank → ℕ := ![33,34,36,40,48,64]
theorem edge2338_span : frame709.space ≤ frame926.space :=
  frame709.inclusion frame926 witness2338 (by decide)
def edge2338 : CertifiedEdge catalog where
  old := 709
  next := 926
  rank := 1
  good := by
    constructor
    · exact edge2338_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2339 : Fin frame709.rank → ℕ := ![33,34,36,40,176,192]
theorem edge2339_span : frame709.space ≤ frame1002.space :=
  frame709.inclusion frame1002 witness2339 (by decide)
def edge2339 : CertifiedEdge catalog where
  old := 709
  next := 1002
  rank := 2
  good := by
    constructor
    · exact edge2339_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2340 : Fin frame710.rank → ℕ := ![49,258,36,24,64,384]
theorem edge2340_span : frame710.space ≤ frame1.space :=
  frame710.inclusion frame1 witness2340 (by decide)
def edge2340 : CertifiedEdge catalog where
  old := 710
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2340_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2341 : Fin frame710.rank → ℕ := ![17,2,4,24,32,64]
theorem edge2341_span : frame710.space ≤ frame934.space :=
  frame710.inclusion frame934 witness2341 (by decide)
def edge2341 : CertifiedEdge catalog where
  old := 710
  next := 934
  rank := 1
  good := by
    constructor
    · exact edge2341_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2342 : Fin frame710.rank → ℕ := ![1,66,4,8,16,96]
theorem edge2342_span : frame710.space ≤ frame942.space :=
  frame710.inclusion frame942 witness2342 (by decide)
def edge2342 : CertifiedEdge catalog where
  old := 710
  next := 942
  rank := 1
  good := by
    constructor
    · exact edge2342_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2343 : Fin frame711.rank → ℕ := ![257,50,36,24,64,384]
theorem edge2343_span : frame711.space ≤ frame1.space :=
  frame711.inclusion frame1 witness2343 (by decide)
def edge2343 : CertifiedEdge catalog where
  old := 711
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2343_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2344 : Fin frame711.rank → ℕ := ![65,2,4,8,16,96]
theorem edge2344_span : frame711.space ≤ frame937.space :=
  frame711.inclusion frame937 witness2344 (by decide)
def edge2344 : CertifiedEdge catalog where
  old := 711
  next := 937
  rank := 1
  good := by
    constructor
    · exact edge2344_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2345 : Fin frame711.rank → ℕ := ![1,18,4,24,32,64]
theorem edge2345_span : frame711.space ≤ frame945.space :=
  frame711.inclusion frame945 witness2345 (by decide)
def edge2345 : CertifiedEdge catalog where
  old := 711
  next := 945
  rank := 1
  good := by
    constructor
    · exact edge2345_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2346 : Fin frame712.rank → ℕ := ![291,36,8,16,64,384]
theorem edge2346_span : frame712.space ≤ frame1.space :=
  frame712.inclusion frame1 witness2346 (by decide)
def edge2346 : CertifiedEdge catalog where
  old := 712
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2346_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2347 : Fin frame712.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2347_span : frame712.space ≤ frame940.space :=
  frame712.inclusion frame940 witness2347 (by decide)
def edge2347 : CertifiedEdge catalog where
  old := 712
  next := 940
  rank := 1
  good := by
    constructor
    · exact edge2347_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2348 : Fin frame712.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2348_span : frame712.space ≤ frame948.space :=
  frame712.inclusion frame948 witness2348 (by decide)
def edge2348 : CertifiedEdge catalog where
  old := 712
  next := 948
  rank := 1
  good := by
    constructor
    · exact edge2348_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2349 : Fin frame713.rank → ℕ := ![19,260,24,288,64,384]
theorem edge2349_span : frame713.space ≤ frame1.space :=
  frame713.inclusion frame1 witness2349 (by decide)
def edge2349 : CertifiedEdge catalog where
  old := 713
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2349_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2350 : Fin frame713.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2350_span : frame713.space ≤ frame941.space :=
  frame713.inclusion frame941 witness2350 (by decide)
def edge2350 : CertifiedEdge catalog where
  old := 713
  next := 941
  rank := 1
  good := by
    constructor
    · exact edge2350_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2351 : Fin frame713.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2351_span : frame713.space ≤ frame949.space :=
  frame713.inclusion frame949 witness2351 (by decide)
def edge2351 : CertifiedEdge catalog where
  old := 713
  next := 949
  rank := 1
  good := by
    constructor
    · exact edge2351_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2352 : Fin frame714.rank → ℕ := ![17,2,4,24,32,64]
theorem edge2352_span : frame714.space ≤ frame940.space :=
  frame714.inclusion frame940 witness2352 (by decide)
def edge2352 : CertifiedEdge catalog where
  old := 714
  next := 940
  rank := 1
  good := by
    constructor
    · exact edge2352_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2353 : Fin frame714.rank → ℕ := ![1,18,20,8,32,64]
theorem edge2353_span : frame714.space ≤ frame949.space :=
  frame714.inclusion frame949 witness2353 (by decide)
def edge2353 : CertifiedEdge catalog where
  old := 714
  next := 949
  rank := 1
  good := by
    constructor
    · exact edge2353_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2354 : Fin frame714.rank → ℕ := ![17,34,36,24,64,128]
theorem edge2354_span : frame714.space ≤ frame1000.space :=
  frame714.inclusion frame1000 witness2354 (by decide)
def edge2354 : CertifiedEdge catalog where
  old := 714
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2354_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2355 : Fin frame715.rank → ℕ := ![17,2,20,8,32,64]
theorem edge2355_span : frame715.space ≤ frame941.space :=
  frame715.inclusion frame941 witness2355 (by decide)
def edge2355 : CertifiedEdge catalog where
  old := 715
  next := 941
  rank := 1
  good := by
    constructor
    · exact edge2355_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2356 : Fin frame715.rank → ℕ := ![1,18,4,24,32,64]
theorem edge2356_span : frame715.space ≤ frame948.space :=
  frame715.inclusion frame948 witness2356 (by decide)
def edge2356 : CertifiedEdge catalog where
  old := 715
  next := 948
  rank := 1
  good := by
    constructor
    · exact edge2356_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2357 : Fin frame715.rank → ℕ := ![33,18,36,24,64,128]
theorem edge2357_span : frame715.space ≤ frame1000.space :=
  frame715.inclusion frame1000 witness2357 (by decide)
def edge2357 : CertifiedEdge catalog where
  old := 715
  next := 1000
  rank := 2
  good := by
    constructor
    · exact edge2357_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2358 : Fin frame716.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2358_span : frame716.space ≤ frame934.space :=
  frame716.inclusion frame934 witness2358 (by decide)
def edge2358 : CertifiedEdge catalog where
  old := 716
  next := 934
  rank := 1
  good := by
    constructor
    · exact edge2358_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2359 : Fin frame716.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2359_span : frame716.space ≤ frame945.space :=
  frame716.inclusion frame945 witness2359 (by decide)
def edge2359 : CertifiedEdge catalog where
  old := 716
  next := 945
  rank := 1
  good := by
    constructor
    · exact edge2359_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2360 : Fin frame716.rank → ℕ := ![131,4,8,16,32,192]
theorem edge2360_span : frame716.space ≤ frame1003.space :=
  frame716.inclusion frame1003 witness2360 (by decide)
def edge2360 : CertifiedEdge catalog where
  old := 716
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2360_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2361 : Fin frame717.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2361_span : frame717.space ≤ frame937.space :=
  frame717.inclusion frame937 witness2361 (by decide)
def edge2361 : CertifiedEdge catalog where
  old := 717
  next := 937
  rank := 1
  good := by
    constructor
    · exact edge2361_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2362 : Fin frame717.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2362_span : frame717.space ≤ frame942.space :=
  frame717.inclusion frame942 witness2362 (by decide)
def edge2362 : CertifiedEdge catalog where
  old := 717
  next := 942
  rank := 1
  good := by
    constructor
    · exact edge2362_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2363 : Fin frame717.rank → ℕ := ![19,4,24,32,64,128]
theorem edge2363_span : frame717.space ≤ frame1003.space :=
  frame717.inclusion frame1003 witness2363 (by decide)
def edge2363 : CertifiedEdge catalog where
  old := 717
  next := 1003
  rank := 2
  good := by
    constructor
    · exact edge2363_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2364 : Fin frame718.rank → ℕ := ![67,260,72,16,288,384]
theorem edge2364_span : frame718.space ≤ frame1.space :=
  frame718.inclusion frame1 witness2364 (by decide)
def edge2364 : CertifiedEdge catalog where
  old := 718
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2364_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2365 : Fin frame718.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2365_span : frame718.space ≤ frame950.space :=
  frame718.inclusion frame950 witness2365 (by decide)
def edge2365 : CertifiedEdge catalog where
  old := 718
  next := 950
  rank := 1
  good := by
    constructor
    · exact edge2365_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2366 : Fin frame718.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2366_span : frame718.space ≤ frame958.space :=
  frame718.inclusion frame958 witness2366 (by decide)
def edge2366 : CertifiedEdge catalog where
  old := 718
  next := 958
  rank := 1
  good := by
    constructor
    · exact edge2366_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2367 : Fin frame719.rank → ℕ := ![387,132,8,16,288,64]
theorem edge2367_span : frame719.space ≤ frame1.space :=
  frame719.inclusion frame1 witness2367 (by decide)
def edge2367 : CertifiedEdge catalog where
  old := 719
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2367_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
