module

public import IntegerMultBounds.Networks.CircuitRouting
public import Mathlib.Data.ZMod.Basic

/-! The bit motif as a finite scalar circuit over `ZMod 2`. Side wires are
ordered label pairs meeting in exactly one coordinate; the `h` central wires
are coordinate sums. There is no all-source-sum wire. The finite instruction
lists restore arbitrary dirty scratch and perform a true data-bank exchange.
Wire enumerations are explicit inputs; sparse wire counts and tape costs are
not established here. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Circuit

/-- Ordered neighboring pairs for the bit motif. For three-element labels,
intersection size one already excludes equal labels. -/
abbrev BitPair {h n : ℕ} (L : Fin n → Finset (Fin h)) :=
  {p : Fin n × Fin n // (L p.1 ∩ L p.2).card = 1}

/-- Exactly one central sum for each ground coordinate. -/
def bitGather {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin h → Fin n → ZMod 2 :=
  fun i t => if i ∈ L t then 1 else 0

/-- A target receives the central sums for its three coordinates. -/
def bitScatter {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin n → Fin h → ZMod 2 :=
  fun s i => if i ∈ L s then 1 else 0

theorem bit_central_coeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) :
    (∑ i, bitScatter L s i * bitGather L i t) = ((L s ∩ L t).card : ZMod 2) := by
  have hh (i : Fin h) :
      bitScatter L s i * bitGather L i t =
        if i ∈ L s ∩ L t then (1 : ZMod 2) else 0 := by
    simp only [bitScatter, bitGather]
    split_ifs <;> simp_all
  simp_rw [hh]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i ∈ L s ∩ L t) = L s ∩ L t := by ext; simp
  rw [hf]
  simp

end IntegerMultBounds.Networks.Circuit
