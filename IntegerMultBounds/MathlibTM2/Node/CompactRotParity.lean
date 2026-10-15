module

public import IntegerMultBounds.MathlibTM2.Node.TopWord
public import IntegerMultBounds.MathlibTM2.Node.KeyPass

/-! # Runtime parity packing for compact rotation offsets

The source word is read in blocks of `q+1` bits. Each first bit is emitted
followed by `b` zero bits. Both block widths are runtime unary parameters.
This module supplies offset construction; unequal-field routing is separate.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

private lemma compactParity_length_flatten {α : Type*} {B : ℕ}
    (xs : List (List α)) (hx : ∀ x ∈ xs, x.length = B) :
    xs.flatten.length = xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hx x (by simp), ih (by intro y hy; exact hx y (by simp [hy]))]
    ring

/-- One source digit contributes its low bit followed by `b` zero bits. -/
def compactParityWord (b : ℕ) (x : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  x.headD (bitSymbol false) :: List.replicate b (bitSymbol false)

/-- On a binary digit, the selected bit is exactly its parity bit. -/
lemma compactParityWord_binSyms (q b x : ℕ) :
    compactParityWord (A := A) b (binSyms (q + 1) x) =
      bitSymbol (x.testBit 0) :: List.replicate b (bitSymbol false) := by
  simp [compactParityWord, binSyms, List.ofFn_succ]

/-- Consume the first symbol and push it onto the output accumulator. -/
def compactParityHead (src dst : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v x => { v with sym := x })
    (.push (.rt dst) (fun v => v.sym.getD (bitSymbol false)) .done)

/-- Read a block, emit its parity and padding, and test for another block. -/
def compactParityStep (e : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (.act (compactParityHead (e 3) (e 2)))
    (.seq (usub (e 5) (e 3) (e 1))
      (.seq (zeroBits (e 6) (e 2) (e 1)) (.act (peekR (e 3)))))

def CompactParityReady (e : Fin 7 → Fin T) (q b : ℕ) (R : Regs T A) : Prop :=
  (R (e 5)).length = q ∧ (R (e 6)).length = b ∧ R (e 1) = []

lemma compactParityReady_frame (e : Fin 7 → Fin T) (he : Function.Injective e) (q b : ℕ) :
    TopWordFrame (e 3) (e 2) (CompactParityReady (A := A) e q b) := by
  intro R l l' h
  simpa [CompactParityReady, he.eq_iff] using h

/-- The per-block program has an exact cost and restores its counters and scratch. -/
theorem compactParityStep_spec (e : Fin 7 → Fin T) (he : Function.Injective e) (q b : ℕ) :
    TopWordSpec body (compactParityStep e) (e 3) (e 2)
      (CompactParityReady e q b) (q + 1) (compactParityWord b) (4*q + 4*b + 10) := by
  intro x rest v S hx hs hready
  obtain ⟨hq, hb, ht⟩ := hready
  cases x with
  | nil => simp at hx
  | cons z zs =>
    have hzs : zs.length = q := by simpa using hx
    let R₁ := Function.update (Function.update S.R (e 3) (zs ++ rest)) (e 2) (z :: S.R (e 2))
    let v₁ : HS T Q A U := { v with sym := some z }
    have h₁ : Exec body (.act (compactParityHead (e 3) (e 2))) (mk v S) 1
        (mk v₁ { S with R := R₁ }) := by
      convert Exec.act (body := body) (compactParityHead (e 3) (e 2)) (mk v S) using 1
      simp [compactParityHead, Action.run, hs, update_rt, R₁, v₁, he.eq_iff]
    obtain ⟨v₂, hu₂, h₂⟩ := usub_exec body (a := e 5) (b := e 3) (t := e 1)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) v₁
      { S with R := R₁ } (by simpa [R₁, he.eq_iff] using ht)
    have htail : (R₁ (e 3)).drop (R₁ (e 5)).length = rest := by
      simp [R₁, he.eq_iff, hq, ← hzs]
    rw [htail] at h₂
    let R₂ := Function.update R₁ (e 3) rest
    obtain ⟨v₃, hu₃, h₃⟩ := zeroBits_exec body (len := e 6) (z := e 2) (t := e 1)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) v₂
      { S with R := R₂ } (by simpa [R₂, R₁, he.eq_iff] using ht)
    let R₃ := Function.update R₂ (e 2) (binSyms (R₂ (e 6)).length 0 ++ R₂ (e 2))
    have h₄ := Exec.act (body := body) (peekR (e 3) : Act T Q A U) (mk v₃ { S with R := R₃ })
    rw [peekR_run] at h₄
    refine ⟨{ v₃ with flag := (R₃ (e 3)).head?.isSome }, hu₃.trans hu₂, ?_,
      Exec.cast (Exec.seq h₁ (Exec.seq h₂ (Exec.seq h₃ h₄))) ?_ ?_⟩
    · simp [R₃, R₂, he.eq_iff]
    · simp [R₂, R₁, he.eq_iff, hq, hb]; omega
    · congr 2
      funext k
      by_cases h3 : k = e 3
      · subst k; simp [R₃, R₂, he.eq_iff]
      · by_cases h2 : k = e 2
        · subst k
          simp [R₃, R₂, R₁, he.eq_iff, hb, compactParityWord, binSyms_zero_right]
        · simp [R₃, R₂, R₁, h3, h2]

/-- Copy the compact source, scan its digits, and return the offset in forward order. -/
def compactParityPack (e : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (copyF (e 0) (e 1) (e 2) (e 1))
    (.seq (moveR (e 2) (e 3) id)
      (.seq (topWords (e 3) (compactParityStep e)) (moveR (e 2) (e 4) id)))

/-- Actual runtime parity packing. Only the offset destination changes; source,
unary block-width parameters and all scratch registers are restored exactly. -/
theorem compactParityPack_exec (e : Fin 7 → Fin T) (he : Function.Injective e)
    (q b : ℕ) (xs : List (List (Fin (A + 4))))
    (hx : ∀ x ∈ xs, x.length = q + 1)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (e 0) = xs.flatten)
    (hready : CompactParityReady e q b S.R)
    (hwork : S.R (e 2) = []) (hcopy : S.R (e 3) = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (compactParityPack e) (mk v S)
        (xs.length * (11*q + 6*b + 20) + 10)
        (mk v' { S with R := Function.update S.R (e 4) ((xs.map (compactParityWord b)).flatten ++ S.R (e 4)) }) := by
  have hlen : xs.flatten.length = xs.length * (q + 1) := compactParity_length_flatten xs hx
  have houtlen : (xs.map (compactParityWord (A := A) b)).flatten.length =
      xs.length * (b + 1) := by
    rw [compactParity_length_flatten (B := b + 1) _ (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      simp [compactParityWord])]
    simp
  obtain ⟨v₁, hu₁, h₁⟩ := copyF_exec body (e 0) (e 1) (e 2) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
    (he.ne (by decide)) v S hready.2.2
  let R₁ := Function.update S.R (e 2) (xs.flatten.reverse)
  have h₁' : Exec body (copyF (e 0) (e 1) (e 2) (e 1)) (mk v S)
      (5 * xs.flatten.length + 4) (mk v₁ { S with R := R₁ }) := by
    simpa [R₁, hsrc, hwork] using h₁
  obtain ⟨v₂, hu₂, h₂⟩ := moveR_exec body (e 2) (e 3) (he.ne (by decide)) id v₁
    { S with R := R₁ }
  let R₂ := Function.update (Function.update S.R (e 2) []) (e 3) xs.flatten
  have h₂' : Exec body (moveR (e 2) (e 3) id) (mk v₁ { S with R := R₁ })
      (2 * xs.flatten.length + 2) (mk v₂ { S with R := R₂ }) := by
    simpa [R₂, R₁, movedR, he.eq_iff, hcopy] using h₂
  have hr₂ : CompactParityReady e q b R₂ := by
    simpa [R₂, CompactParityReady, he.eq_iff] using hready
  let v₃ : HS T Q A U := { v₂ with flag := xs.flatten.head?.isSome }
  have h₃ : Exec body (.act (peekR (e 3))) (mk v₂ { S with R := R₂ }) 1
      (mk v₃ { S with R := R₂ }) := by
    simpa [v₃, R₂, peekR_run] using
      (Exec.act (body := body) (peekR (e 3) : Act T Q A U) (mk v₂ { S with R := R₂ }))
  obtain ⟨v₄, hu₄, h₄⟩ := topWords_loop body (he.ne (by decide))
    (compactParityReady_frame e he q b) (by omega : 1 ≤ q + 1)
    (compactParityStep_spec body e he q b) xs v₃ { S with R := R₂ }
    hx (by simp [R₂]) hr₂ rfl
  let out := (xs.map (compactParityWord (A := A) b)).flatten
  let R₄ := Function.update (Function.update R₂ (e 3) []) (e 2) out.reverse
  have h₄' : Exec body (.loop (·.flag) (compactParityStep e))
      (mk v₃ { S with R := R₂ }) (xs.length * (4*q + 4*b + 10 + 1) + 1)
      (mk v₄ { S with R := R₄ }) := by
    simpa [R₄, out, R₂, he.eq_iff] using h₄
  obtain ⟨v₅, hu₅, h₅⟩ := moveR_exec body (e 2) (e 4) (he.ne (by decide)) id v₄
    { S with R := R₄ }
  refine ⟨v₅, hu₅.trans (hu₄.trans (hu₂.trans hu₁)),
    Exec.cast (Exec.seq h₁' (Exec.seq h₂' (Exec.seq (Exec.seq h₃ h₄') h₅))) ?_ ?_⟩
  · simp [R₄, out, hlen, houtlen]; ring
  · congr 2
    funext k
    by_cases hk4 : k = e 4
    · subst k; simp [movedR, R₄, R₂, he.eq_iff, out]
    · by_cases hk2 : k = e 2
      · subst k; simp [movedR, R₄, R₂, he.eq_iff, hwork]
      · by_cases hk3 : k = e 3
        · subst k; simp [movedR, R₄, R₂, he.eq_iff, hcopy]
        · simp [movedR, R₄, R₂, hk4, hk2, hk3]

end
end IntegerMultBounds.MathlibTM2.Node
