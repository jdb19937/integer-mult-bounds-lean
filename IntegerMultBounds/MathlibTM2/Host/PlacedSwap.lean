module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import IntegerMultBounds.MathlibTM2.Host.Placed

/-!
# Rectangular interchange on placed host registers

`placedSwapProg` runs the vendored binary rectangular interchange machine
(`BinaryInterchangeRun.program`, through the alphabet encoding `Alphabet.widen prime K` and the
state embedding `liftQ`) on an injective family `ι : Fin (swapT t₀) → Fin T` of host registers,
for any host tape count `T ≥ swapT t₀`. Register `ι (reg i)` is caller tape `i` of the machine,
the other registers `ι j` are its private tapes. The machine is placed on the registers `ι` with
`Placement.placed`, so every transition writes back the scanned symbol and stays on every other
register (`placed_idle_injective`).

The program
1. pushes a blank onto the right stack of every unplaced register, so that the simulation leaves
   these stacks exactly as they are (`foreign_exec_frame`);
2. moves the first symbol (`separator`) of each of the five header registers to its left stack;
3. runs the placed machine with `foreign`;
4. normalizes the placed registers (`normList`);
5. pops the blank pushed in step 1.

Only the placed registers are normalized or constrained by hypotheses. The time bound depends on
the unplaced registers only through the tape count `T`: each simulated transition costs `T + 4`
host steps (`foreign` scans every host tape), and steps 1 and 5 cost one step per unplaced
register.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The placement of the interchange machine's bank on host registers `ι`. -/
abbrev swapPlacement {t₀ T : ℕ} (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι)
    (hT : swapT t₀ ≤ T) : Fin (swapT t₀ + (T - swapT t₀)) ≃ Fin T :=
  InjectivePlacement.placement ι hι (Nat.add_sub_cancel' hT)

/-- The interchange machine over the host alphabet, placed on host registers `ι`. -/
def placedSwapMachine {t₀ T Q : ℕ} (K : ℕ) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T) :
    Program T Q (prime + K) :=
  Placement.placed (liftQ (swapMachine K hd pay hi) hQ) (swapPlacement ι hι hT)

/-- Interchange on host registers `ι`: mark every unplaced register, shift each header register
one cell, run the placed interchange machine, normalize the placed registers, unmark. -/
def placedSwapProg {t₀ T Q K : ℕ} {U F : Type} (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T) :
    Pr F T Q (prime + K) U :=
  .seq (markList (unplaced ι))
    (.seq (shiftList (List.ofFn fun k => ι (reg (hd k))))
      (.seq (foreign (placedSwapMachine K hd pay hi hQ ι hι hT))
        (.seq (normList (List.ofFn ι)) (dropList (unplaced ι)))))

/-- Running the interchange on host registers `ι`. Register `ι (reg pay)` holds the payload bits,
register `ι (reg (hd k))` the encoded header `separator :: bits` of `hs k`; the placed left stacks
and the placed private registers are empty; every other placed caller register holds non-blank
symbols of the vendored alphabet. Afterwards the payload register holds the interchanged bits,
the placed left stacks are empty, and every other stack is unchanged. -/
theorem placedSwapProg_run {t₀ T Q K : ℕ} {U F : Type} (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L (ι j) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G B h d hs +
        6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * swapT t₀ + 15 ∧
      Exec body (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun y => if y ∈ List.ofFn ι then [] else S.L y
          R := Function.update S.R (ι (reg pay))
            (List.ofFn fun z => bitSymbol (BinaryAdjacentWidthInterchange.transpose x z)) }) := by
  classical
  set e := Alphabet.widen prime K with he_def
  set pe := swapPlacement ι hι hT with hpe
  -- every placed register holds non-blank symbols of the vendored alphabet
  have hgood : ∀ j, ∀ s ∈ S.R (ι j), s ≠ blank ∧ s.val < prime + 4 := by
    intro j s hs'
    by_cases hj : j.val < t₀
    · have hji : j = reg (⟨j.val, hj⟩ : Fin t₀) := Fin.ext rfl
      rw [hji] at hs'
      by_cases hip : (⟨j.val, hj⟩ : Fin t₀) = pay
      · rw [hip, hpay, List.mem_ofFn] at hs'
        obtain ⟨z, rfl⟩ := hs'
        exact bitSymbol_good _
      · by_cases hk : ∃ k, hd k = ⟨j.val, hj⟩
        · obtain ⟨k, hk⟩ := hk
          rw [← hk, hhdr k] at hs'
          simp only [List.mem_cons, List.mem_map] at hs'
          rcases hs' with rfl | ⟨b, _, rfl⟩
          · exact separator_good
          · exact bitSymbol_good _
        · exact hother _ hip (fun k hk' => hk ⟨k, hk'⟩) s hs'
    · rw [hpriv j (by omega)] at hs'
      simp at hs'
  -- the payload register is not a header register
  have hpay_hd : ∀ k, hd k ≠ pay := by
    intro k hk
    have hvol : 0 < BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B := by
      unfold BinaryAdjacentWidthInterchange.volume; positivity
    have h1 := congrArg (fun l => l[0]?) (hhdr k)
    rw [hk, hpay] at h1
    simp only [List.getElem?_ofFn, hvol, dite_true, List.getElem?_cons_zero,
      Option.some.injEq] at h1
    have h2 := congrArg Fin.val h1
    revert h2
    cases x ⟨0, hvol⟩ <;> simp [bitSymbol, separator]
  -- the caller bank seen by the interchange machine
  let caller : Tapes t₀ prime :=
    ⟨fun i => if ∃ k, hd k = i then 1 else 0, fun i => wordTape ((S.R (ι (reg i))).map e.decode)⟩
  have htapes : ∀ k, caller.tape (hd k) = RadixZeroFill.encodedBinary (hs k) := by
    intro k
    show wordTape ((S.R (ι (reg (hd k)))).map e.decode) = _
    rw [hhdr k, encodedBinary_eq]
    simp [e, Function.comp_def]
  have hheads : ∀ k, caller.head (hd k) = 1 := fun k => by
    show (if ∃ k', hd k' = hd k then (1 : ℤ) else 0) = 1
    rw [ite_eq_left ⟨k, rfl⟩]
  have ht :
      caller.tape pay = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
    show wordTape ((S.R (ι (reg pay))).map e.decode) = _
    rw [BinaryRadixRangePrepareAlphabet.word, putWord_blank_zero, hpay, List.map_ofFn]
    simp [e, Function.comp_def]
  have hh : caller.head pay = 0 := by
    show (if ∃ k, hd k = pay then (1 : ℤ) else 0) = 0
    rw [ite_eq_right (fun ⟨k, hk⟩ => hpay_hd k hk)]
  have hrun := BinaryInterchangeRun.runs caller hd pay hi P G B h d hs hhd hdh hv hc hP hG hB
    htapes hheads x ht hh
  have hM := HoareTime.liftQ hQ (Alphabet.map_hoare e hrun)
  -- step 1: mark the unplaced registers
  have hun : ∀ j, ι j ∉ unplaced ι := fun j hm => (mem_unplaced ι _).1 hm j rfl
  have he₀ := markList_exec body (unplaced ι) (unplaced_nodup ι) v S
  set S₀ : Stacks T (prime + K) :=
    { S with R := fun y => if y ∈ unplaced ι then blank :: S.R y else S.R y } with hS₀
  -- step 2: shift the header registers
  set l₀ : List (Fin T) := List.ofFn fun k => ι (reg (hd k)) with hl₀
  have hnd₀ : l₀.Nodup := by
    rw [hl₀, List.nodup_ofFn]
    intro a b hab
    exact hi (BinaryInterchangeRun.slot_injective (hι hab))
  have hmem : ∀ y, y ∈ l₀ ↔ ∃ k, ι (reg (hd k)) = y := fun y => List.mem_ofFn
  obtain ⟨v₁, hu₁, he₁⟩ := shiftList_exec body l₀ hnd₀ v S₀
  set S₁ : Stacks T (prime + K) := { S₀ with
    L := fun i => if i ∈ l₀ then (S₀.R i).head?.getD blank :: S₀.L i else S₀.L i
    R := fun i => if i ∈ l₀ then (S₀.R i).tail else S₀.R i } with hS₁
  have hS₁hdr : ∀ k, S₁.L (ι (reg (hd k))) = [separator] ∧
      S₁.R (ι (reg (hd k))) = (hs k).map bitSymbol := by
    intro k
    have hm : ι (reg (hd k)) ∈ l₀ := (hmem _).2 ⟨k, rfl⟩
    simp [S₁, S₀, hm, hun, hL, hhdr k]
  have hS₁oth : ∀ j, (∀ k, reg (hd k) ≠ j) → S₁.L (ι j) = [] ∧ S₁.R (ι j) = S.R (ι j) := by
    intro j hj
    have hm : ι j ∉ l₀ := fun hm => by
      obtain ⟨k, hk⟩ := (hmem _).1 hm
      exact hj k (hι hk)
    simp [S₁, S₀, hm, hun, hL]
  have hS₁un : ∀ y, (∀ j, ι j ≠ y) → S₁.L y = S.L y ∧ S₁.R y = blank :: S.R y := by
    intro y hy
    have hm : y ∉ l₀ := fun hm => by
      obtain ⟨k, hk⟩ := (hmem _).1 hm
      exact hy _ hk
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    simp [S₁, S₀, hm, hu]
  have hS₁len : ∀ j, (S₁.L (ι j)).length + (S₁.R (ι j)).length = (S.R (ι j)).length := by
    intro j
    by_cases hk : ∃ k, reg (hd k) = j
    · obtain ⟨k, rfl⟩ := hk
      rw [(hS₁hdr k).1, (hS₁hdr k).2, hhdr k]
      simp
      omega
    · rw [(hS₁oth j fun k hk' => hk ⟨k, hk'⟩).1, (hS₁oth j fun k hk' => hk ⟨k, hk'⟩).2]
      simp
  -- the host bank represented by `S₁`
  let w₀ : Tapes T (prime + K) := ⟨fun _ => 0, fun y z => readAt blank (S₁.L y) (S₁.R y) z⟩
  let W := Placement.replace pe w₀ (Alphabet.mapTapes e (BinaryInterchangeRun.input caller))
  have hrep : RepT W S₁.L S₁.R := by
    intro y z
    by_cases hy : ∃ j, ι j = y
    · obtain ⟨j, rfl⟩ := hy
      rw [InjectivePlacement.replace_tape_slot, InjectivePlacement.replace_head_slot]
      obtain ⟨hhead, htape⟩ := input_ext caller j
      show e.encode ((BinaryInterchangeRun.input caller).tape j z) =
        readAt blank (S₁.L (ι j)) (S₁.R (ι j)) (z - (BinaryInterchangeRun.input caller).head j)
      rw [hhead, htape]
      by_cases hj : j.val < t₀
      · rw [dite_eq_left hj, dite_eq_left hj]
        obtain ⟨i, rfl⟩ : ∃ i : Fin t₀, j = reg i := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
        change e.encode (wordTape ((S.R (ι (reg i))).map e.decode) z) =
          readAt blank (S₁.L (ι (reg i))) (S₁.R (ι (reg i))) (z - caller.head i)
        rw [encode_wordTape_decode _ (fun s hs => (hgood _ s hs).2) z]
        by_cases hk : ∃ k, hd k = i
        · obtain ⟨k, rfl⟩ := hk
          rw [(hS₁hdr k).1, (hS₁hdr k).2, hheads k, hhdr k, readAt_single]
        · have hc0 : caller.head i = 0 := ite_eq_right hk
          have hoth := hS₁oth (reg i) (fun k hk' => hk ⟨k, BinaryInterchangeRun.slot_injective hk'⟩)
          rw [hoth.1, hoth.2, hc0, sub_zero, readAt_nil_left]
      · rw [dite_eq_right hj, dite_eq_right hj]
        have hoth := hS₁oth j (fun k hk' => hj (hk' ▸ (hd k).isLt))
        rw [hoth.1, hoth.2, hpriv j (by omega), readAt_nil_left, wordTape_nil]
        rfl
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j, hj⟩
      rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hy',
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hy']
      show readAt blank (S₁.L y) (S₁.R y) z = readAt blank (S₁.L y) (S₁.R y) (z - 0)
      rw [sub_zero]
  have hpre := Placement.hoare_at hM pe W (by
    refine ⟨_, rfl, ?_⟩
    exact Placement.active_replace pe w₀ _)
  -- step 3: run the placed interchange machine
  obtain ⟨v₂, S₂, W', ⟨w', ⟨orig, horig, rfl⟩, hW'⟩, hrep', hu₂, hinp₂, hout₂, hlen₂, hfr₂,
      m₂, hm₂, he₂⟩ :=
    foreign_exec_frame body _ (placed_idle_injective _ ι hι _) hpre v₁ S₁ W rfl hrep
  subst horig
  -- the placed registers after the run
  set out : List (Fin (prime + K + 4)) :=
    List.ofFn fun z => bitSymbol (BinaryAdjacentWidthInterchange.transpose x z) with hout
  set R' := Function.update S.R (ι (reg pay)) out with hR'
  have hR'ι : ∀ j, j ≠ reg pay → R' (ι j) = S.R (ι j) := fun j hj =>
    Function.update_of_ne (fun h' => hj (hι h')) _ _
  have hfinal : ∀ j z, (Alphabet.mapTapes e (BinaryInterchangeRun.input
      (SharedPlacementAlphabet.setTape caller pay (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) 0))).tape j z =
      wordTape (R' (ι j)) z := by
    intro j z
    obtain ⟨_, htape⟩ := input_ext (SharedPlacementAlphabet.setTape caller pay
      (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) 0) j
    show e.encode ((BinaryInterchangeRun.input _).tape j z) = _
    rw [htape]
    by_cases hj : j.val < t₀
    · rw [dite_eq_left hj]
      obtain ⟨i, rfl⟩ : ∃ i : Fin t₀, j = reg i := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      change e.encode (Function.update caller.tape pay (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) i z) = _
      by_cases hip : i = pay
      · subst hip
        rw [Function.update_self, hR', Function.update_self, BinaryRadixRangePrepareAlphabet.word,
          putWord_blank_zero, encode_wordTape, List.map_ofFn]
        rfl
      · have hr : reg i ≠ reg pay := fun h' => hip (BinaryInterchangeRun.slot_injective h')
        rw [Function.update_of_ne hip, hR'ι _ hr]
        exact encode_wordTape_decode _ (fun s hs => (hgood _ s hs).2) z
    · rw [dite_eq_right hj]
      have hr : j ≠ reg pay := fun h' => hj (h' ▸ pay.isLt)
      rw [hR'ι _ hr, hpriv j (by omega), wordTape_nil]
      rfl
  have hfree : ∀ j, blank ∉ R' (ι j) := by
    intro j hb
    by_cases hj : j = reg pay
    · subst hj
      rw [hR', Function.update_self, hout, List.mem_ofFn] at hb
      obtain ⟨z, hz⟩ := hb
      exact (bitSymbol_good _).1 hz
    · rw [hR'ι _ hj] at hb
      exact (hgood j blank hb).1 rfl
  have hsweep : ∀ j, sweep (S₂.L (ι j)) (S₂.R (ι j)) = R' (ι j) := by
    intro j
    refine filter_window (S₂.L (ι j)) (S₂.R (ι j)) (W'.head (ι j)) _ (hfree j) (fun z => ?_)
    have := hrep' (ι j) z
    rw [hW', InjectivePlacement.replace_tape_slot] at this
    rw [← hfinal j z, hW']
    exact this
  -- the unplaced registers after the run
  have hS₂un : ∀ y, (∀ j, ι j ≠ y) → S₂.L y = S.L y ∧ S₂.R y = blank :: S.R y := by
    intro y hy
    have h₁ := hS₁un y hy
    have h₂ := idle_stacks_eq (hfr₂ y hy) (by rw [h₁.2]; exact List.cons_ne_nil _ _)
    exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
  -- step 4: normalize the placed registers
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ :=
    normList_exec body (List.ofFn ι) (List.nodup_ofFn.2 hι) v₂ S₂
  -- step 5: unmark the unplaced registers
  have he₄ := dropList_exec body (unplaced ι) (unplaced_nodup ι) v₃ { S₂ with
    L := fun i => if i ∈ List.ofFn ι then [] else S₂.L i
    R := fun i => if i ∈ List.ofFn ι then sweep (S₂.L i) (S₂.R i) else S₂.R i }
  refine ⟨v₃, ((unplaced ι).length + 1) + ((l₀.length + 1) + (m₂ + (n₃ +
    ((unplaced ι).length + 1)))), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))) rfl ?_⟩
  · rw [List.map_ofFn, List.sum_ofFn] at hn₃
    set k := BinaryInterchangeRun.cost P G B h d hs
    have hsum : ∑ j, ((fun i => 6 * ((S₂.L i).length + (S₂.R i).length) + 6) ∘ ι) j ≤
        ∑ j, (6 * (S.R (ι j)).length + (12 * k + 6)) := by
      apply Finset.sum_le_sum
      intro j _
      have h1 := hlen₂ (ι j)
      rw [hS₁len] at h1
      simp only [Function.comp_apply]
      omega
    have hR : ∑ j : Fin (swapT t₀), (6 * (S.R (ι j)).length + (12 * k + 6)) =
        6 * ∑ j, (S.R (ι j)).length + swapT t₀ * (12 * k + 6) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have key : k * (T + 5) + swapT t₀ * (12 * k + 6) =
        (T + 12 * swapT t₀ + 5) * k + 6 * swapT t₀ := by ring
    have hl : l₀.length = 5 := by simp [hl₀]
    have hu := unplaced_length_le ι
    rw [hl]
    omega
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hinp₂
    · exact hout₂
    · funext y
      by_cases hy : y ∈ List.ofFn ι
      · simp only [hy, ite_true]
      · have hy' : ∀ j, ι j ≠ y := fun j hj => hy (List.mem_ofFn.2 ⟨j, hj⟩)
        simp only [hy, ite_false, (hS₂un y hy').1]
    · funext y
      by_cases hy : ∃ j, ι j = y
      · obtain ⟨j, rfl⟩ := hy
        have hm : ι j ∈ List.ofFn ι := List.mem_ofFn.2 ⟨j, rfl⟩
        simp only [hun j, hm, ite_true, ite_false]
        exact hsweep j
      · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j, hj⟩
        have hm : y ∉ List.ofFn ι := fun hm => hy (List.mem_ofFn.1 hm)
        have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy'
        simp only [hu, hm, ite_true, ite_false, (hS₂un y hy').2, List.tail_cons]
        rw [hR', Function.update_of_ne (fun h' => hy' _ h'.symm)]

/-- `placedSwapProg_run` with every left stack empty, and the payload output as a list function
of the payload input. -/
theorem placedSwapProg_exec {t₀ T Q K : ℕ} {U F : Type} (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G B h d hs +
        6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * swapT t₀ + 15 ∧
      Exec body (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun _ => []
          R := Function.update S.R (ι (reg pay))
            (swapList P (2 ^ h) G (2 ^ d) B blank (S.R (ι (reg pay)))) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := placedSwapProg_run body hd pay hi hQ ι hι hT P G B h d hs hhd
    hdh hv hc hP hG hB x v S (fun j => hL (ι j)) hpriv hhdr hpay hother
  refine ⟨v', m, hu, hm, ?_⟩
  have hL' : (fun y => if y ∈ List.ofFn ι then [] else S.L y) = fun _ => [] := by
    funext y; split_ifs <;> simp [hL]
  rw [hL'] at he
  rw [hpay, ← transpose_bits_eq_swapList]
  exact he

end

end IntegerMultBounds.MathlibTM2.Host
