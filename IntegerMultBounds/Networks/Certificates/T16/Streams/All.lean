module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check0
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check1
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check2
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check3
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check4
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check5
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check6
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check7
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check8
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check9
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check10
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check11
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check12
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check13
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check14
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Check15

/-! The eight-stream composition of every selected replica and port. For each of the 16
replicas and 112 ports, the expanded data schedule, with all hosted helper slices and idle
remainder children, is accepted by the stream check; by `run_of_accepts` it is then exactly the
full frame `C_all` on every one of the eight data streams, for every operator homomorphism. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

def groups : ℕ → List GroupData
  | 0 => groups0
  | 1 => groups1
  | 2 => groups2
  | 3 => groups3
  | 4 => groups4
  | 5 => groups5
  | 6 => groups6
  | 7 => groups7
  | 8 => groups8
  | 9 => groups9
  | 10 => groups10
  | 11 => groups11
  | 12 => groups12
  | 13 => groups13
  | 14 => groups14
  | 15 => groups15
  | _ => []

theorem accepts_of_all {G : List GroupData} {r : ℕ}
    (h : ((G.zip ports).all fun gp => groupAccepts template localPair localReverse gp.2 gp.1 r) = true)
    (hG : G.length = 112) (a : ℕ) (ha : a < 112) :
    groupAccepts template localPair localReverse (ports.getD a ⟨[], (0, 0), 0, []⟩)
      (G.getD a ⟨[], []⟩) r = true := by
  have hp : ports.length = 112 := by decide
  have hz : a < (G.zip ports).length := by simp [hG, hp, ha]
  have hm := List.all_eq_true.mp h _ (List.getElem_mem hz)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hG ▸ ha),
    List.getElem?_eq_getElem (hp ▸ ha)] using hm

/-- **All 1,792 groups accept.** -/
theorem all_accepts (r : ℕ) (hr : r < 16) (a : ℕ) (ha : a < 112) :
    groupAccepts template localPair localReverse (ports.getD a ⟨[], (0, 0), 0, []⟩)
      ((groups r).getD a ⟨[], []⟩) r = true := by
  match r, hr with
  | 0, _ => exact accepts_of_all replica0_accepts groups0_length a ha
  | 1, _ => exact accepts_of_all replica1_accepts groups1_length a ha
  | 2, _ => exact accepts_of_all replica2_accepts groups2_length a ha
  | 3, _ => exact accepts_of_all replica3_accepts groups3_length a ha
  | 4, _ => exact accepts_of_all replica4_accepts groups4_length a ha
  | 5, _ => exact accepts_of_all replica5_accepts groups5_length a ha
  | 6, _ => exact accepts_of_all replica6_accepts groups6_length a ha
  | 7, _ => exact accepts_of_all replica7_accepts groups7_length a ha
  | 8, _ => exact accepts_of_all replica8_accepts groups8_length a ha
  | 9, _ => exact accepts_of_all replica9_accepts groups9_length a ha
  | 10, _ => exact accepts_of_all replica10_accepts groups10_length a ha
  | 11, _ => exact accepts_of_all replica11_accepts groups11_length a ha
  | 12, _ => exact accepts_of_all replica12_accepts groups12_length a ha
  | 13, _ => exact accepts_of_all replica13_accepts groups13_length a ha
  | 14, _ => exact accepts_of_all replica14_accepts groups14_length a ha
  | 15, _ => exact accepts_of_all replica15_accepts groups15_length a ha
  | _ + 16, h => omega

end IntegerMultBounds.Networks.Certificates.T16.Streams
