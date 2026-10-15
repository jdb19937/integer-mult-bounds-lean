module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Checker

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def witness1920 : Fin frame550.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1920_span : frame550.space ≤ frame754.space :=
  frame550.inclusion frame754 witness1920 (by decide)
def edge1920 : CertifiedEdge catalog where
  old := 550
  next := 754
  rank := 1
  good := by
    constructor
    · exact edge1920_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1921 : Fin frame550.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1921_span : frame550.space ≤ frame755.space :=
  frame550.inclusion frame755 witness1921 (by decide)
def edge1921 : CertifiedEdge catalog where
  old := 550
  next := 755
  rank := 1
  good := by
    constructor
    · exact edge1921_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1922 : Fin frame551.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1922_span : frame551.space ≤ frame756.space :=
  frame551.inclusion frame756 witness1922 (by decide)
def edge1922 : CertifiedEdge catalog where
  old := 551
  next := 756
  rank := 1
  good := by
    constructor
    · exact edge1922_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1923 : Fin frame551.rank → ℕ := ![3,4,8,16,32,64]
theorem edge1923_span : frame551.space ≤ frame757.space :=
  frame551.inclusion frame757 witness1923 (by decide)
def edge1923 : CertifiedEdge catalog where
  old := 551
  next := 757
  rank := 1
  good := by
    constructor
    · exact edge1923_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1924 : Fin frame552.rank → ℕ := ![5,6,8]
theorem edge1924_span : frame552.space ≤ frame211.space :=
  frame552.inclusion frame211 witness1924 (by decide)
def edge1924 : CertifiedEdge catalog where
  old := 552
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge1924_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1925 : Fin frame552.rank → ℕ := ![5,6,48]
theorem edge1925_span : frame552.space ≤ frame556.space :=
  frame552.inclusion frame556 witness1925 (by decide)
def edge1925 : CertifiedEdge catalog where
  old := 552
  next := 556
  rank := 3
  good := by
    constructor
    · exact edge1925_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1926 : Fin frame552.rank → ℕ := ![1,2,8]
theorem edge1926_span : frame552.space ≤ frame600.space :=
  frame552.inclusion frame600 witness1926 (by decide)
def edge1926 : CertifiedEdge catalog where
  old := 552
  next := 600
  rank := 1
  good := by
    constructor
    · exact edge1926_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1927 : Fin frame553.rank → ℕ := ![1,2,8]
theorem edge1927_span : frame553.space ≤ frame211.space :=
  frame553.inclusion frame211 witness1927 (by decide)
def edge1927 : CertifiedEdge catalog where
  old := 553
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge1927_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1928 : Fin frame553.rank → ℕ := ![33,34,48]
theorem edge1928_span : frame553.space ≤ frame557.space :=
  frame553.inclusion frame557 witness1928 (by decide)
def edge1928 : CertifiedEdge catalog where
  old := 553
  next := 557
  rank := 3
  good := by
    constructor
    · exact edge1928_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1929 : Fin frame553.rank → ℕ := ![1,2,8]
theorem edge1929_span : frame553.space ≤ frame601.space :=
  frame553.inclusion frame601 witness1929 (by decide)
def edge1929 : CertifiedEdge catalog where
  old := 553
  next := 601
  rank := 1
  good := by
    constructor
    · exact edge1929_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1930 : Fin frame554.rank → ℕ := ![1,6,8]
theorem edge1930_span : frame554.space ≤ frame211.space :=
  frame554.inclusion frame211 witness1930 (by decide)
def edge1930 : CertifiedEdge catalog where
  old := 554
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge1930_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1931 : Fin frame554.rank → ℕ := ![9,2,12]
theorem edge1931_span : frame554.space ≤ frame618.space :=
  frame554.inclusion frame618 witness1931 (by decide)
def edge1931 : CertifiedEdge catalog where
  old := 554
  next := 618
  rank := 1
  good := by
    constructor
    · exact edge1931_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1932 : Fin frame554.rank → ℕ := ![1,70,48]
theorem edge1932_span : frame554.space ≤ frame763.space :=
  frame554.inclusion frame763 witness1932 (by decide)
def edge1932 : CertifiedEdge catalog where
  old := 554
  next := 763
  rank := 4
  good := by
    constructor
    · exact edge1932_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1933 : Fin frame555.rank → ℕ := ![5,2,8]
theorem edge1933_span : frame555.space ≤ frame211.space :=
  frame555.inclusion frame211 witness1933 (by decide)
def edge1933 : CertifiedEdge catalog where
  old := 555
  next := 211
  rank := 1
  good := by
    constructor
    · exact edge1933_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1934 : Fin frame555.rank → ℕ := ![1,10,12]
theorem edge1934_span : frame555.space ≤ frame620.space :=
  frame555.inclusion frame620 witness1934 (by decide)
def edge1934 : CertifiedEdge catalog where
  old := 555
  next := 620
  rank := 1
  good := by
    constructor
    · exact edge1934_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1935 : Fin frame555.rank → ℕ := ![69,2,48]
theorem edge1935_span : frame555.space ≤ frame762.space :=
  frame555.inclusion frame762 witness1935 (by decide)
def edge1935 : CertifiedEdge catalog where
  old := 555
  next := 762
  rank := 4
  good := by
    constructor
    · exact edge1935_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1936 : Fin frame556.rank → ℕ := ![65,66,4,8,16,32]
theorem edge1936_span : frame556.space ≤ frame750.space :=
  frame556.inclusion frame750 witness1936 (by decide)
def edge1936 : CertifiedEdge catalog where
  old := 556
  next := 750
  rank := 1
  good := by
    constructor
    · exact edge1936_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1937 : Fin frame556.rank → ℕ := ![1,2,4,72,16,96]
theorem edge1937_span : frame556.space ≤ frame751.space :=
  frame556.inclusion frame751 witness1937 (by decide)
def edge1937 : CertifiedEdge catalog where
  old := 556
  next := 751
  rank := 1
  good := by
    constructor
    · exact edge1937_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1938 : Fin frame557.rank → ℕ := ![1,2,68,8,80,32]
theorem edge1938_span : frame557.space ≤ frame752.space :=
  frame557.inclusion frame752 witness1938 (by decide)
def edge1938 : CertifiedEdge catalog where
  old := 557
  next := 752
  rank := 1
  good := by
    constructor
    · exact edge1938_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1939 : Fin frame557.rank → ℕ := ![65,66,68,72,80,96]
theorem edge1939_span : frame557.space ≤ frame753.space :=
  frame557.inclusion frame753 witness1939 (by decide)
def edge1939 : CertifiedEdge catalog where
  old := 557
  next := 753
  rank := 1
  good := by
    constructor
    · exact edge1939_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1940 : Fin frame558.rank → ℕ := ![9,2,12]
theorem edge1940_span : frame558.space ≤ frame240.space :=
  frame558.inclusion frame240 witness1940 (by decide)
def edge1940 : CertifiedEdge catalog where
  old := 558
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1940_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1941 : Fin frame558.rank → ℕ := ![53,18,24]
theorem edge1941_span : frame558.space ≤ frame562.space :=
  frame558.inclusion frame562 witness1941 (by decide)
def edge1941 : CertifiedEdge catalog where
  old := 558
  next := 562
  rank := 3
  good := by
    constructor
    · exact edge1941_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1942 : Fin frame558.rank → ℕ := ![3,4,8]
theorem edge1942_span : frame558.space ≤ frame616.space :=
  frame558.inclusion frame616 witness1942 (by decide)
def edge1942 : CertifiedEdge catalog where
  old := 558
  next := 616
  rank := 1
  good := by
    constructor
    · exact edge1942_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1943 : Fin frame559.rank → ℕ := ![1,4,8]
theorem edge1943_span : frame559.space ≤ frame240.space :=
  frame559.inclusion frame240 witness1943 (by decide)
def edge1943 : CertifiedEdge catalog where
  old := 559
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1943_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1944 : Fin frame559.rank → ℕ := ![1,36,56]
theorem edge1944_span : frame559.space ≤ frame563.space :=
  frame559.inclusion frame563 witness1944 (by decide)
def edge1944 : CertifiedEdge catalog where
  old := 559
  next := 563
  rank := 3
  good := by
    constructor
    · exact edge1944_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1945 : Fin frame559.rank → ℕ := ![3,4,8]
theorem edge1945_span : frame559.space ≤ frame617.space :=
  frame559.inclusion frame617 witness1945 (by decide)
def edge1945 : CertifiedEdge catalog where
  old := 559
  next := 617
  rank := 1
  good := by
    constructor
    · exact edge1945_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1946 : Fin frame560.rank → ℕ := ![1,2,12]
theorem edge1946_span : frame560.space ≤ frame240.space :=
  frame560.inclusion frame240 witness1946 (by decide)
def edge1946 : CertifiedEdge catalog where
  old := 560
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1946_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1947 : Fin frame560.rank → ℕ := ![5,2,8]
theorem edge1947_span : frame560.space ≤ frame602.space :=
  frame560.inclusion frame602 witness1947 (by decide)
def edge1947 : CertifiedEdge catalog where
  old := 560
  next := 602
  rank := 1
  good := by
    constructor
    · exact edge1947_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1948 : Fin frame560.rank → ℕ := ![11,68,112]
theorem edge1948_span : frame560.space ≤ frame751.space :=
  frame560.inclusion frame751 witness1948 (by decide)
def edge1948 : CertifiedEdge catalog where
  old := 560
  next := 751
  rank := 4
  good := by
    constructor
    · exact edge1948_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1949 : Fin frame561.rank → ℕ := ![3,4,8]
theorem edge1949_span : frame561.space ≤ frame240.space :=
  frame561.inclusion frame240 witness1949 (by decide)
def edge1949 : CertifiedEdge catalog where
  old := 561
  next := 240
  rank := 1
  good := by
    constructor
    · exact edge1949_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1950 : Fin frame561.rank → ℕ := ![15,16,32]
theorem edge1950_span : frame561.space ≤ frame586.space :=
  frame561.inclusion frame586 witness1950 (by decide)
def edge1950 : CertifiedEdge catalog where
  old := 561
  next := 586
  rank := 3
  good := by
    constructor
    · exact edge1950_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide

def witness1951 : Fin frame561.rank → ℕ := ![3,4,8]
theorem edge1951_span : frame561.space ≤ frame604.space :=
  frame561.inclusion frame604 witness1951 (by decide)
def edge1951 : CertifiedEdge catalog where
  old := 561
  next := 604
  rank := 1
  good := by
    constructor
    · exact edge1951_span
    constructor
    · rw [CertifiedFrame.dimension, CertifiedFrame.dimension]
      decide
    · decide


end IntegerMultBounds.Networks.Certificates.T16.Geometry
