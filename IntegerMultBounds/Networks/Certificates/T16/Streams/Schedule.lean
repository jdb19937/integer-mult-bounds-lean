module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Sound

/-! The selected T16 data schedule as eight-stream programs, one per replica and port. Phase
vectors are coefficients over the port's orthonormal basis `B_q ⊕ I`: index 0 is `q`, indices
1..8 the other low basis vectors, and index `j ≥ 9` the coordinate vector `e_j`. Data stream
`2p` is `X_p` and `2p+1` is `Y_p`; a stream at canonical level `s` has frame
`wt(u ∧ [0, 9+8s)) - side·[u·q]`, and the sources start at `C_q`, the targets at `I`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

/-- One event of the global template. -/
inductive TEvent where
  | local (stage replica : ℕ)
  | idle (replica pair c0 c1 : ℕ)
  | bridge (replica dst src : ℕ) (c : ℤ)
  | terminalY (replica : ℕ) (pairs : List ℕ)
  | terminal (replica pairs : ℕ)

/-- Port data: its basis, the weights mod 4 of its low basis vectors, the terminal `Y`
translation and the idle-child translations, both in basis coordinates. -/
structure PortData where
  basis : List ℕ
  wtlow : Vec
  terminal : ℕ
  idleTranslations : List ℕ

/-- Group data: hosted helper slices `(stage * 16 + replica, stream, axes)` and the idle
remainder axes of each child, as basis-index masks. -/
structure GroupData where
  hosted : List (ℕ × ℕ × ℕ)
  idle : List (ℕ × ℕ)

def toStream (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

def toPair (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

/-- The coefficient vector of `[u·q]`. -/
def qVec : Vec := (1, 0)

/-- The canonical data frame at level `l - 1` (so `l = 0` is the initial level). -/
def frameVec (P : PortData) (l side : ℕ) : Vec :=
  if l = 0 then (if side = 0 then qVec else Vec.zero)
  else
    let base := Vec.add P.wtlow (2 ^ (9 + 8 * (l - 1)) - 2 ^ 9, 0)
    if side = 0 then base else base.add qVec.neg

def dataEvents (P : PortData) (stage : ℕ) (pair : ℕ) (reverse : Bool) : List Event :=
  let x := toStream (2 * pair)
  let y := toStream (2 * pair + 1)
  [.phase x (frameVec P stage 0).neg, .phase y (frameVec P stage 1).neg,
    if reverse then .shear x y (-1) else .shear y x 1,
    .phase x (frameVec P (stage + 1) 0), .phase y (frameVec P (stage + 1) 1)]

def hostedEvents (G : GroupData) (slot : ℕ) : List Event :=
  G.hosted.filterMap fun h => if h.1 = slot then some (.phase (toStream h.2.1) (h.2.2, 0)) else none

def idleEvent (P : PortData) (G : GroupData) (pair side child : ℕ) : Event :=
  .phase (toStream (2 * pair + side))
    (Vec.add ((G.idle.lookup child).getD 0, 0) (0, P.idleTranslations.getD child 0))

def expand (P : PortData) (G : GroupData) (replica : ℕ) (localPair : ℕ → ℕ)
    (localReverse : ℕ → Bool) : TEvent → List Event
  | .local s r => hostedEvents G (s * 16 + r) ++
      (if r = replica then dataEvents P s (localPair s) (localReverse s) else [])
  | .idle r p c0 c1 => if r = replica then [idleEvent P G p 0 c0, idleEvent P G p 1 c1] else []
  | .bridge r d s c => if r = replica then
      [.shear (toStream (2 * d)) (toStream (2 * s)) c,
        .shear (toStream (2 * s + 1)) (toStream (2 * d + 1)) (-c)] else []
  | .terminalY r ps => if r = replica then ps.map fun p => .phase (toStream (2 * p + 1)) (0, P.terminal)
      else []
  | .terminal r n => if r = replica then (List.range n).map fun p => .exchange (toPair p) else []

def groupEvents (template : List TEvent) (localPair : ℕ → ℕ) (localReverse : ℕ → Bool)
    (P : PortData) (G : GroupData) (replica : ℕ) : List Event :=
  template.flatMap (expand P G replica localPair localReverse)

def startFrame (P : PortData) (i : Fin 8) : Vec := frameVec P 0 (i.val % 2)

/-- The full frame `C_all`, in basis coordinates. -/
def fullFrame (P : PortData) : Vec := frameVec P 9 0

def groupAccepts (template : List TEvent) (localPair : ℕ → ℕ) (localReverse : ℕ → Bool)
    (P : PortData) (G : GroupData) (replica : ℕ) : Bool :=
  accepts (groupEvents template localPair localReverse P G replica) (startFrame P) (fullFrame P)

end IntegerMultBounds.Networks.Certificates.T16.Streams
