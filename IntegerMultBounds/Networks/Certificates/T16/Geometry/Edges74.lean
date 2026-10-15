module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness2368 : Fin frame719.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2368_span : frame719.space ≤ frame953.space :=
  frame719.inclusion frame953 witness2368 (by decide)
def edge2368 : CertifiedEdge catalog where
  old := 719
  next := 953
  rank := 1
  good := by
    constructor
    · exact edge2368_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2369 : Fin frame719.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2369_span : frame719.space ≤ frame961.space :=
  frame719.inclusion frame961 witness2369 (by decide)
def edge2369 : CertifiedEdge catalog where
  old := 719
  next := 961
  rank := 1
  good := by
    constructor
    · exact edge2369_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2370 : Fin frame720.rank → ℕ := ![193,258,132,72,16,288]
theorem edge2370_span : frame720.space ≤ frame1.space :=
  frame720.inclusion frame1 witness2370 (by decide)
def edge2370 : CertifiedEdge catalog where
  old := 720
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2370_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2371 : Fin frame720.rank → ℕ := ![1,66,4,8,16,96]
theorem edge2371_span : frame720.space ≤ frame956.space :=
  frame720.inclusion frame956 witness2371 (by decide)
def edge2371 : CertifiedEdge catalog where
  old := 720
  next := 956
  rank := 1
  good := by
    constructor
    · exact edge2371_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2372 : Fin frame720.rank → ℕ := ![65,2,4,72,16,32]
theorem edge2372_span : frame720.space ≤ frame964.space :=
  frame720.inclusion frame964 witness2372 (by decide)
def edge2372 : CertifiedEdge catalog where
  old := 720
  next := 964
  rank := 1
  good := by
    constructor
    · exact edge2372_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2373 : Fin frame721.rank → ℕ := ![257,194,132,72,16,288]
theorem edge2373_span : frame721.space ≤ frame1.space :=
  frame721.inclusion frame1 witness2373 (by decide)
def edge2373 : CertifiedEdge catalog where
  old := 721
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2373_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2374 : Fin frame721.rank → ℕ := ![1,66,4,72,16,32]
theorem edge2374_span : frame721.space ≤ frame957.space :=
  frame721.inclusion frame957 witness2374 (by decide)
def edge2374 : CertifiedEdge catalog where
  old := 721
  next := 957
  rank := 1
  good := by
    constructor
    · exact edge2374_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2375 : Fin frame721.rank → ℕ := ![65,2,4,8,16,96]
theorem edge2375_span : frame721.space ≤ frame965.space :=
  frame721.inclusion frame965 witness2375 (by decide)
def edge2375 : CertifiedEdge catalog where
  old := 721
  next := 965
  rank := 1
  good := by
    constructor
    · exact edge2375_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2376 : Fin frame722.rank → ℕ := ![195,132,72,16,32,256]
theorem edge2376_span : frame722.space ≤ frame1.space :=
  frame722.inclusion frame1 witness2376 (by decide)
def edge2376 : CertifiedEdge catalog where
  old := 722
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2376_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2377 : Fin frame722.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2377_span : frame722.space ≤ frame956.space :=
  frame722.inclusion frame956 witness2377 (by decide)
def edge2377 : CertifiedEdge catalog where
  old := 722
  next := 956
  rank := 1
  good := by
    constructor
    · exact edge2377_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2378 : Fin frame722.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2378_span : frame722.space ≤ frame965.space :=
  frame722.inclusion frame965 witness2378 (by decide)
def edge2378 : CertifiedEdge catalog where
  old := 722
  next := 965
  rank := 1
  good := by
    constructor
    · exact edge2378_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2379 : Fin frame723.rank → ℕ := ![259,132,136,16,288,192]
theorem edge2379_span : frame723.space ≤ frame1.space :=
  frame723.inclusion frame1 witness2379 (by decide)
def edge2379 : CertifiedEdge catalog where
  old := 723
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2379_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2380 : Fin frame723.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2380_span : frame723.space ≤ frame957.space :=
  frame723.inclusion frame957 witness2380 (by decide)
def edge2380 : CertifiedEdge catalog where
  old := 723
  next := 957
  rank := 1
  good := by
    constructor
    · exact edge2380_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2381 : Fin frame723.rank → ℕ := ![3,4,8,16,32,64]
theorem edge2381_span : frame723.space ≤ frame964.space :=
  frame723.inclusion frame964 witness2381 (by decide)
def edge2381 : CertifiedEdge catalog where
  old := 723
  next := 964
  rank := 1
  good := by
    constructor
    · exact edge2381_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2382 : Fin frame724.rank → ℕ := ![65,386,132,72,16,288]
theorem edge2382_span : frame724.space ≤ frame1.space :=
  frame724.inclusion frame1 witness2382 (by decide)
def edge2382 : CertifiedEdge catalog where
  old := 724
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2382_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2383 : Fin frame724.rank → ℕ := ![1,66,68,8,16,32]
theorem edge2383_span : frame724.space ≤ frame950.space :=
  frame724.inclusion frame950 witness2383 (by decide)
def edge2383 : CertifiedEdge catalog where
  old := 724
  next := 950
  rank := 1
  good := by
    constructor
    · exact edge2383_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2384 : Fin frame724.rank → ℕ := ![65,2,4,72,16,32]
theorem edge2384_span : frame724.space ≤ frame961.space :=
  frame724.inclusion frame961 witness2384 (by decide)
def edge2384 : CertifiedEdge catalog where
  old := 724
  next := 961
  rank := 1
  good := by
    constructor
    · exact edge2384_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2385 : Fin frame725.rank → ℕ := ![385,66,132,72,16,288]
theorem edge2385_span : frame725.space ≤ frame1.space :=
  frame725.inclusion frame1 witness2385 (by decide)
def edge2385 : CertifiedEdge catalog where
  old := 725
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2385_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2386 : Fin frame725.rank → ℕ := ![1,66,4,72,16,32]
theorem edge2386_span : frame725.space ≤ frame953.space :=
  frame725.inclusion frame953 witness2386 (by decide)
def edge2386 : CertifiedEdge catalog where
  old := 725
  next := 953
  rank := 1
  good := by
    constructor
    · exact edge2386_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2387 : Fin frame725.rank → ℕ := ![65,2,68,8,16,32]
theorem edge2387_span : frame725.space ≤ frame958.space :=
  frame725.inclusion frame958 witness2387 (by decide)
def edge2387 : CertifiedEdge catalog where
  old := 725
  next := 958
  rank := 1
  good := by
    constructor
    · exact edge2387_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2388 : Fin frame726.rank → ℕ := ![257,258,100,360,304,384]
theorem edge2388_span : frame726.space ≤ frame1.space :=
  frame726.inclusion frame1 witness2388 (by decide)
def edge2388 : CertifiedEdge catalog where
  old := 726
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2388_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2389 : Fin frame726.rank → ℕ := ![65,66,4,72,80,96]
theorem edge2389_span : frame726.space ≤ frame966.space :=
  frame726.inclusion frame966 witness2389 (by decide)
def edge2389 : CertifiedEdge catalog where
  old := 726
  next := 966
  rank := 1
  good := by
    constructor
    · exact edge2389_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2390 : Fin frame726.rank → ℕ := ![1,2,36,40,16,64]
theorem edge2390_span : frame726.space ≤ frame974.space :=
  frame726.inclusion frame974 witness2390 (by decide)
def edge2390 : CertifiedEdge catalog where
  old := 726
  next := 974
  rank := 1
  good := by
    constructor
    · exact edge2390_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2391 : Fin frame727.rank → ℕ := ![129,130,36,296,304,64]
theorem edge2391_span : frame727.space ≤ frame1.space :=
  frame727.inclusion frame1 witness2391 (by decide)
def edge2391 : CertifiedEdge catalog where
  old := 727
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2391_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2392 : Fin frame727.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2392_span : frame727.space ≤ frame969.space :=
  frame727.inclusion frame969 witness2392 (by decide)
def edge2392 : CertifiedEdge catalog where
  old := 727
  next := 969
  rank := 1
  good := by
    constructor
    · exact edge2392_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2393 : Fin frame727.rank → ℕ := ![1,2,4,72,80,32]
theorem edge2393_span : frame727.space ≤ frame977.space :=
  frame727.inclusion frame977 witness2393 (by decide)
def edge2393 : CertifiedEdge catalog where
  old := 727
  next := 977
  rank := 1
  good := by
    constructor
    · exact edge2393_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2394 : Fin frame728.rank → ℕ := ![129,130,196,456,400,160]
theorem edge2394_span : frame728.space ≤ frame1.space :=
  frame728.inclusion frame1 witness2394 (by decide)
def edge2394 : CertifiedEdge catalog where
  old := 728
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2394_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2395 : Fin frame728.rank → ℕ := ![65,66,68,72,80,96]
theorem edge2395_span : frame728.space ≤ frame972.space :=
  frame728.inclusion frame972 witness2395 (by decide)
def edge2395 : CertifiedEdge catalog where
  old := 728
  next := 972
  rank := 1
  good := by
    constructor
    · exact edge2395_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2396 : Fin frame728.rank → ℕ := ![1,2,68,72,16,32]
theorem edge2396_span : frame728.space ≤ frame980.space :=
  frame728.inclusion frame980 witness2396 (by decide)
def edge2396 : CertifiedEdge catalog where
  old := 728
  next := 980
  rank := 1
  good := by
    constructor
    · exact edge2396_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2397 : Fin frame729.rank → ℕ := ![129,130,260,8,80,352]
theorem edge2397_span : frame729.space ≤ frame1.space :=
  frame729.inclusion frame1 witness2397 (by decide)
def edge2397 : CertifiedEdge catalog where
  old := 729
  next := 1
  rank := 3
  good := by
    constructor
    · exact edge2397_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2398 : Fin frame729.rank → ℕ := ![65,66,4,8,16,32]
theorem edge2398_span : frame729.space ≤ frame973.space :=
  frame729.inclusion frame973 witness2398 (by decide)
def edge2398 : CertifiedEdge catalog where
  old := 729
  next := 973
  rank := 1
  good := by
    constructor
    · exact edge2398_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness2399 : Fin frame729.rank → ℕ := ![1,2,4,8,80,96]
theorem edge2399_span : frame729.space ≤ frame981.space :=
  frame729.inclusion frame981 witness2399 (by decide)
def edge2399 : CertifiedEdge catalog where
  old := 729
  next := 981
  rank := 1
  good := by
    constructor
    · exact edge2399_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
