module

public import IntegerMultBounds.MathlibTM2.Routing.ReadOrdered
public import IntegerMultBounds.MathlibTM2.Routing.SourceGather

/-!
# Compact offsets from arbitrarily ordered sources

The fixed descriptor interpreter is followed by the existing spread program.
Both source and descriptor are restored; gathered bits are cleared after use.
The compact output is the value required by the modular control load. The
caller supplies the descriptor and compact mask and must charge their setup.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- The descriptor's source bits, extended by zero beyond its length. -/
def sourceBit {W n : ℕ} (s : Fin n → Fin W) (x j : ℕ) : Bool :=
  if hj : j < n then x.testBit (s ⟨j, hj⟩).val else false

/-- The physical compact word is exactly the packed source value used by the
arithmetic shear, including arbitrary descriptor order. -/
theorem readOffset_value {W n : ℕ} (s : Fin n → Fin W) (x G : ℕ) :
    IntegerMultBounds.Compact.Radix.pack ((2 : ℤ) ^ G)
      (Coordinates.read s (fun k => x.testBit k.val)) =
        (placeVal n (fun j => j * G) (sourceBit s x) : ℤ) := by
  let pos : ℕ → ℕ := fun j => if hj : j < n then (s ⟨j, hj⟩).val else 0
  have hread : Coordinates.read s (fun k => x.testBit k.val) =
      Coordinates.read (fun j : Fin n => pos j.val) x.testBit := by
    unfold Coordinates.read
    congr 1
    funext j
    simp [pos]
  rw [hread, packed_read_eq n G pos x]
  congr 1
  unfold placeVal
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < n := Finset.mem_range.mp hj
  simp [sourceBit, pos, hj']

/-- Prepare a compact modular offset from an ordered source table. -/
def readOffset (src desc ts tm dst g mask out cs : Fin T) : Pr P T Q A U :=
  .seq (readRows src desc ts tm dst g cs)
    (.seq (spread g mask ts tm dst out) (bclear g))

/-- Full physical source-offset execution with arbitrary source order and explicit
cost. The gathered temporary and all scan/spread scratch return empty. -/
theorem readOffset_exec {src desc ts tm dst g mask out cs : Fin T}
    (hr : [src, desc, ts, tm, dst, g].Nodup) (hsr : GSRegs g mask ts tm dst out)
    (_hframe : out ≠ src ∧ out ≠ desc)
    {W n G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (s : Fin n → Fin W) (x : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = (binBits W x).map bitSymbol)
    (hd : S.R desc = (sourceTable (List.ofFn s)).flatten.map bitSymbol)
    (hm : S.R mask = (binBits (n * G) (maskVal n (fun j => j * G))).map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = [])
    (hg : S.R g = []) (hout : S.R out = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ n * (6 * W + 10) + 8 * (n * G) + 16 ∧
      Exec body (readOffset src desc ts tm dst g mask out cs) (mk v S) m
        (mk v' { S with
          R := Function.update S.R out ((binBits (n * G)
            (placeVal n (fun j => j * G) (sourceBit s x))).map bitSymbol) }) := by
  have hn := hsr
  simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, _, _, _, _⟩ := hn
  let bits := (List.ofFn fun j : Fin n => x.testBit (s j)).map (bitSymbol (a := A))
  obtain ⟨v₁, hu₁, he₁⟩ := readOrdered_exec body (cs := cs) hr hW
    (fun j : Fin W => x.testBit j.val) (List.ofFn s) v S hs hd hts htm hdst
  rw [hg, List.append_nil, List.map_ofFn] at he₁
  let R₁ := Function.update S.R g bits
  have hmono : StrictMono (fun j : ℕ => j * G) := fun _ _ h =>
    Nat.mul_lt_mul_of_pos_right h hG
  have hbound : ∀ j < n, j * G < n * G := fun _ h =>
    Nat.mul_lt_mul_of_pos_right h hG
  let f : ℕ → Bool := sourceBit s x
  have hbits : (List.ofFn fun j : Fin n => x.testBit (s j)) =
      List.ofFn fun j : Fin n => f j.val := by simp [f, sourceBit]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := spread_exec body hsr
    (binBits (n * G) (maskVal n (fun j => j * G))) (List.ofFn fun j : Fin n => f j.val)
    (by rw [count_maskVal hmono hbound]; simp) v₁ { S with R := R₁ }
    (by simp [R₁, Ne.symm a1, hm])
    (by
      simp only [R₁, Function.update_self]
      change (List.ofFn fun j : Fin n => x.testBit (s j)).map bitSymbol = _
      rw [hbits])
    (by simp [R₁, Ne.symm a2, hts]) (by simp [R₁, Ne.symm a3, htm])
    (by simp [R₁, Ne.symm a4, hdst])
  rw [spreadL_mask hmono hbound] at he₂
  let offset := (binBits (n * G) (placeVal n (fun j => j * G) f)).map (bitSymbol (a := A))
  let R₂ := Function.update R₁ out offset
  have hout₁ : R₁ out = [] := by simp [R₁, Ne.symm a5, hout]
  dsimp only at he₂
  rw [hout₁, List.append_nil] at he₂
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body g v₂ { S with R := R₂ }
  have hlen : (R₂ g).length = n := by simp [R₂, R₁, a5, bits]
  have hrestore : Function.update R₂ g [] = Function.update S.R out offset := by
    funext k
    by_cases hk : k = g
    · subst k; simp [a5, hg]
    · simp [R₂, R₁, Function.update_apply, hk]
  refine ⟨v₃, ((List.ofFn s).length * (6 * W + 8) + 6) +
    (m₂ + (2 * (R₂ g).length + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hlen]
    simp only [List.length_ofFn, binBits] at hm₂ ⊢
    simp only [Nat.mul_add]
    omega
  · exact Exec.seq he₁ (Exec.seq he₂ (Exec.cast he₃ rfl (by rw [hrestore])))

end IntegerMultBounds.MathlibTM2.Routing
