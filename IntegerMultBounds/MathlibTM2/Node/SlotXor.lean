module

public import IntegerMultBounds.MathlibTM2.Node.FixPass
public import IntegerMultBounds.MathlibTM2.Node.RotPass
public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Layer.Enc

/-!
# The packed slot XOR

`slotXorProg hι hQ par src st x y z` adds, column by column, slot `x` of the active region to
slot `y` (modulo `2`) on the array held by the stream register `src`, for static slot indices
`x, y, z : Fin m` (`m = 25³`, all distinct).

**Address layout.** The array is `Z : ZArr (Fin R × Fin r) n`, stored as `encZ A w Z` (row by row,
`2^n` records of `r w` symbols per row). Active bit `i` is at `e i = a₀ + ρ + K i`, so slot `j`
occupies the address bits `[a₀ + j L, a₀ + (j + 1) L)`, `L = K k`, with its column `c < k` at
`a₀ + j L + ρ + K c`. The target is `pullM e (sxXorCol x y) Z`, where `sxXorCol x y a` adds
coordinate `x` of the column `a` to coordinate `y` (`sxMap`, `sx_pullM_xorCol`).

**The rectangle.** With the three slots sorted as `lo < mid < hi` (`sxPos`), the address of a
record splits into `n3 = a₀ + lo L` low bits, slot `lo` (chunk slot `2`), `n2 = (mid - lo - 1) L`
gap bits, slot `mid` (chunk slot `1`), `n1 = (hi - mid - 1) L` gap bits, slot `hi` (chunk slot `0`),
and `n0 = n - (a₀ + (hi + 1) L)` high bits, which with the row index form the outer coordinate:
`N₀ = R 2^n0`, `N₁ = 2^n1`, `N₂ = 2^n2`, `N₃ = 2^n3` (`sxN0` … `sxN3`). The physical order
`sxSigma x y z` sends chunk slot `p` to the name (`x = 0`, `y = 1`, `z = 2`) whose slot index is
`sxPos x y z p`. The packed
target `xorSel L K ρ k` on this rectangle moves the record at rank `2^n u + a` to
`2^n u + addrNum (sxMap e x y) a` (`sx_addrPerm_xorSel`), so moving the records of `Z` by it gives
the records of the target (`sx_moveRecs_xorSel`).

**Registers.** `SXReg` names the registers of the machine, placed by an injective
`ι : SXReg → Fin T`; `SXPar` names the unary parameter registers `K, ρ, a₀, L, rows, n, rw`, placed
by an injective `par` with a range disjoint from that of `ι` (`SxEnv`). The stream register `src`
and the scan slot `st` lie outside the range of `ι`. At rest every register `ι x` is empty. The
setup (`sxSetup`, 38 stages `sxStageProg`, one register per stage, `sxStage`) builds, from the
parameters: the unary field lengths `n3, n2, n1, n0`; the row count in canonical binary (`rbin`,
`sxBinConv`, amortized by `GrowingCounterData.amortized_cost`) and its bit count `rb`; the eight
fields of the record index counter `cf` (`idxLen n0 n1 n2 n3 L rb`); the counters `ctrB` (`r w`
symbols), `ctrK` (`n + rb`), `ctrKB` (`r w + n + rb`), `cnt` (`R 2^n`); the binary numbers `bbin`
(three keyed record lengths) and `lbin` (`L`); the masks `msel` (`selMask K ρ (k - 1)`), `mgrd`
(the guard mask) and `mtop` (`2^(ρ + (k - 1) K)`), built by `sxMask` and `bitMask` on the
`ρ + L - K` bits below `K - ρ` zero bits; and the five headers of each of the three interchange
banks `swp c` (`sxHs`, one bank per pair class `sxCls` of exchanged chunk slots). The register file
after `s` stages is `sxFill ι (sxBc A d) s R₀`. The cleanup (`sxCleanup`) empties the 38 registers.

**Program.** `sxSetup`; `keyPass` (each record gains its destination key under `idealT`); the
packed program `prog σ` (`sxInstrs`: `swapPass` on bank `sxCls a b` for `Instr.swap a b`, `rotPass`
for `Instr.rot neg b`); `repairPass` (the stream of `idealT`); `fixPass` (`topFix`); `sxCleanup`.
Since `xorSel = topFix * idealT` (`xorSel_eq`), the passes move the records by `xorSel`.

**Main theorem** (`slotXor_exec`). Alphabet `prime + Ka` with `14 ≤ prime + Ka`, state count
`swapStates sxHd sxPay sxHd_inj ≤ Q`, `ρ < K`, `L = K k`, `1 ≤ k`, `1 ≤ R`, `1 ≤ r w`,
`a₀ + m L ≤ n`, `e i = a₀ + ρ + K i`; every left stack empty, `src` holding `encZ A w Z`, the
parameter registers holding `K, ρ, a₀, L, R, n, r w` symbols, every register `ι x` empty. Then
`src` ends holding `encZ A w (pullM e (sxXorCol x y) Z)`, every other register as it started,
`user` kept, within `10 · sxSwapReal d T + sxNatCost d T (sxBad d)` steps: `sxSwapReal` is the
vendored interchange bound `3 C (T + 12 t + 5) V max(1, L)^τ` (`C = swapConst`, `t = swapT 6`,
`V = R 2^n (r w + n + rb)` keyed symbols) for each of at most ten interchanges, and `sxNatCost` is
explicit: the setup and the cleanup, the key, repair and fix passes (each `O(M (r w + k' + 1))` with
`M = R 2^n`, `k' = n + rb`, the repair with an extra `13 |Bad| k' (r w + k' + 1)` for the
`sxBad d` exceptional addresses of margin `1`), eight rotation passes, and the linear parts of the
interchanges. In closed form (`sxNatCost_le`, `slotXor_exec_le`), `sxNatCost d T (sxBad d)` is at
most `20000 M (r w + k' + 1) + 13 |Bad| k' (r w + k' + 1) + 20 T + 60 t + 20000`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer.PackedXor
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ recList coeffList addrBits addrNum pullAddr pullM colBits merge
  ofCols toCols bitIdx)



/-! ### Canonical binary counters on a register -/

section Binary

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- The canonical binary digits of `x`, least significant first: `x` increments from `[]`. -/
def sxBits (x : ℕ) : List Bool := GrowingCounterData.advance x []

lemma sx_advance_succ (n : ℕ) (bs : List Bool) :
    GrowingCounterData.advance (n + 1) bs =
      GrowingCounterData.increment (GrowingCounterData.advance n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
      show GrowingCounterData.advance (n + 1) (GrowingCounterData.increment bs) = _
      rw [ih]; rfl

lemma sxBits_succ (x : ℕ) : sxBits (x + 1) = GrowingCounterData.increment (sxBits x) :=
  sx_advance_succ x []

lemma value_sxBits (x : ℕ) : Counter.value (sxBits x) = x :=
  GrowingCounterData.empty_value x

lemma canonical_sxBits (x : ℕ) : GrowingCounterData.Canonical (sxBits x) :=
  GrowingCounterData.advance_canonical x [] (Or.inl rfl)

lemma length_sxBits_le (x : ℕ) : (sxBits x).length ≤ x := by
  induction x with
  | zero => simp [sxBits, GrowingCounterData.advance]
  | succ x ih =>
      rw [sxBits_succ]
      have := (GrowingCounterData.increment_length (sxBits x)).2
      omega

lemma lt_two_pow_length_sxBits (x : ℕ) : x < 2 ^ (sxBits x).length := by
  have := Counter.value_lt (sxBits x)
  rwa [value_sxBits] at this

lemma sxBits_ne_nil {x : ℕ} (hx : 0 < x) : sxBits x ≠ [] := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [sxBits_succ]
  exact GrowingCounterData.increment_ne_nil _

/-- The carry steps of the increments from `[]` sum to half the vendored amortized cost. -/
lemma sx_totalCost_eq_sum (x : ℕ) (bs : List Bool) :
    GrowingCounterData.totalCost x bs =
      2 * ∑ i ∈ Finset.range x, GrowingCounterData.carrySteps (GrowingCounterData.advance i bs) := by
  induction x generalizing bs with
  | zero => simp [GrowingCounterData.totalCost]
  | succ x ih =>
      rw [GrowingCounterData.totalCost, ih, Finset.sum_range_succ']
      simp only [GrowingCounterData.advance]
      ring

lemma sx_sum_carrySteps_le (x : ℕ) :
    ∑ i ∈ Finset.range x, GrowingCounterData.carrySteps (sxBits i) ≤ 2 * x := by
  have h1 := GrowingCounterData.amortized_cost x []
  rw [sx_totalCost_eq_sum] at h1
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at h1
  unfold sxBits
  omega

/-- Test whether the top of `d` is `bitSymbol true`. -/
def sxTopTrue (d : Fin T) : Act T Q A U :=
  .peek (.rt d) (fun v o => { v with flag := decide (o = some (bitSymbol true)) }) .done

/-- One carry: pop the `bitSymbol true` on top of `d`, push `bitSymbol false` onto `t`, test. -/
def sxCarryStep (d t : Fin T) : Act T Q A U :=
  .pop (.rt d) (fun v _ => v) (.push (.rt t) (fun _ => bitSymbol false) (sxTopTrue d))

/-- End of a carry: replace the top `bitSymbol false` of `d` (or nothing) by `bitSymbol true`. -/
def sxSetTrue (d : Fin T) : Act T Q A U :=
  .pop (.rt d) (fun v _ => v) (.push (.rt d) (fun _ => bitSymbol true) .done)

/-- Increment the canonical counter on `d` (least significant bit on top), through the empty
`t`. -/
def sxBinInc (d t : Fin T) : Pr P T Q A U :=
  .seq (.act (sxTopTrue d)) (.seq (.loop (·.flag) (.act (sxCarryStep d t)))
    (.seq (.act (sxSetTrue d)) (moveR t d id)))

lemma sx_bitSymbol_inj {b c : Bool} : (bitSymbol b : Fin (A + 4)) = bitSymbol c ↔ b = c := by
  cases b <;> cases c <;> simp [bitSymbol, Fin.ext_iff]

lemma sx_carry_loop (d t : Fin T) (hdt : d ≠ t) (rest : List Bool)
    (hrest : rest.head? ≠ some true) :
    ∀ (j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R d = (List.replicate j true ++ rest).map bitSymbol →
      v.flag = decide ((S.R d).head? = some (bitSymbol true)) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (sxCarryStep d t))) (mk v S) (2 * j + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R d (rest.map bitSymbol)) t
              (List.replicate j (bitSymbol false) ++ S.R t) }) := by
  intro j
  induction j with
  | zero =>
      intro v S hd hf
      refine ⟨v, rfl, ?_⟩
      have hS : ({ S with
          R := Function.update (Function.update S.R d (rest.map bitSymbol)) t
            (List.replicate 0 (bitSymbol false) ++ S.R t) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only [List.replicate_zero, List.nil_append] at hd ⊢
          rw [← hd, Function.update_eq_self, Function.update_eq_self]
      rw [hS]
      refine .loop_false ?_
      simp only [mk_var, hf, hd, List.replicate_zero, List.nil_append, decide_eq_false_iff_not]
      intro h
      cases rest with
      | nil => simp at h
      | cons b r =>
          simp only [List.map_cons, List.head?_cons, Option.some.injEq, sx_bitSymbol_inj] at h
          subst h
          simp at hrest
  | succ j ih =>
      intro v S hd hf
      set R' := Function.update (Function.update S.R d (S.R d).tail) t
        (bitSymbol false :: S.R t) with hR'
      have hrun : (sxCarryStep d t : Act T Q A U).run (mk v S) =
          mk { v with flag := decide ((R' d).head? = some (bitSymbol true)) }
            { S with R := R' } := by
        simp only [sxCarryStep, sxTopTrue, Action.run, mk_stk, get_rt, update_rt, mk_var, store_mk,
          Function.update_of_ne hdt.symm]
        rfl
      have hd' : R' d = (List.replicate j true ++ rest).map bitSymbol := by
        simp [hR', Function.update_of_ne hdt, hd, List.replicate_succ]
      obtain ⟨v', hu, he⟩ := ih { v with flag := decide ((R' d).head? = some (bitSymbol true)) }
        { S with R := R' } hd' rfl
      refine ⟨v', by rw [hu], ?_⟩
      have hft : v.flag = true := by
        rw [hf, hd]; simp [List.replicate_succ]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft
        (hrun ▸ Exec.act (body := body) (sxCarryStep d t) (mk v S)) he) (by ring) ?_
      congr 2
      funext k
      by_cases hk : k = t
      · subst hk
        simp [hR', List.replicate_succ']
      · by_cases hk' : k = d
        · subst hk'; simp [hk, hR']
        · simp [hk, hk', hR']

lemma sx_exists_run : ∀ bs : List Bool, ∃ j rest, bs = List.replicate j true ++ rest ∧
    rest.head? ≠ some true
  | [] => ⟨0, [], rfl, by simp⟩
  | false :: bs => ⟨0, false :: bs, rfl, by simp⟩
  | true :: bs => by
      obtain ⟨j, rest, h1, h2⟩ := sx_exists_run bs
      exact ⟨j + 1, rest, by rw [h1]; rfl, h2⟩

lemma sx_carrySteps_run (j : ℕ) (rest : List Bool) (hrest : rest.head? ≠ some true) :
    GrowingCounterData.carrySteps (List.replicate j true ++ rest) = j + 1 := by
  induction j with
  | zero =>
      cases rest with
      | nil => rfl
      | cons b r =>
          cases b
          · rfl
          · simp at hrest
  | succ j ih => simp [List.replicate_succ, GrowingCounterData.carrySteps, ih]

lemma sx_increment_run (j : ℕ) (rest : List Bool) :
    GrowingCounterData.increment (List.replicate j true ++ rest) =
      List.replicate j false ++ GrowingCounterData.increment rest := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, GrowingCounterData.increment, ih]

/-- One increment of the canonical counter `bs` on `d`: exactly `4 · carrySteps bs + 1` steps. -/
theorem sxBinInc_exec (d t : Fin T) (hdt : d ≠ t) (bs : List Bool) (v : HS T Q A U)
    (S : Stacks T A) (hd : S.R d = bs.map bitSymbol) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (sxBinInc d t) (mk v S) (4 * GrowingCounterData.carrySteps bs + 1)
        (mk v' { S with
          R := Function.update S.R d ((GrowingCounterData.increment bs).map bitSymbol) }) := by
  obtain ⟨j, rest, rfl, hrest⟩ := sx_exists_run bs
  have hcarry := sx_carrySteps_run j rest hrest
  have hinc := sx_increment_run j rest
  have he₀ := Exec.act (body := body) (sxTopTrue d) (mk v S)
  have hr₀ : (sxTopTrue d : Act T Q A U).run (mk v S) =
      mk { v with flag := decide ((S.R d).head? = some (bitSymbol true)) } S := rfl
  rw [hr₀] at he₀
  obtain ⟨v₁, hu₁, he₁⟩ := sx_carry_loop body d t hdt rest hrest j
    { v with flag := decide ((S.R d).head? = some (bitSymbol true)) } S hd rfl
  set R₁ := Function.update (Function.update S.R d (rest.map bitSymbol)) t
    (List.replicate j (bitSymbol false) ++ S.R t) with hR₁
  have he₂ := Exec.act (body := body) (sxSetTrue d) (mk v₁ { S with R := R₁ })
  set R₂ := Function.update R₁ d (bitSymbol true :: (rest.map bitSymbol).tail) with hR₂
  have hr₂ : (sxSetTrue d : Act T Q A U).run (mk v₁ { S with R := R₁ }) = mk v₁ { S with R := R₂ } := by
    simp [sxSetTrue, Action.run, update_rt, hR₂, hR₁, Function.update_of_ne hdt]
  rw [hr₂] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t d hdt.symm id v₁ { S with R := R₂ }
  refine ⟨v₃, by rw [hu₃, hu₁], Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · have : (R₂ t).length = j := by
      simp [hR₂, hR₁, Function.update_of_ne hdt.symm, ht]
    simp only [this, hcarry]
    ring
  · have hrinc : (bitSymbol true :: (rest.map bitSymbol).tail : List (Fin (A + 4))) =
        (GrowingCounterData.increment rest).map bitSymbol := by
      cases rest with
      | nil => rfl
      | cons b r =>
          cases b
          · rfl
          · simp at hrest
    have hR₂t : R₂ t = List.replicate j (bitSymbol false) := by
      simp [hR₂, hR₁, Function.update_of_ne hdt.symm, ht]
    have hR₂d : R₂ d = (GrowingCounterData.increment rest).map bitSymbol := by
      simp [hR₂, hrinc]
    have hR₂o : ∀ k, k ≠ d → k ≠ t → R₂ k = S.R k := fun k h1 h2 => by
      simp [hR₂, hR₁, h1, h2]
    congr 2
    funext k
    simp only [movedR, List.map_id, hR₂t]
    by_cases hk : k = d
    · subst hk
      rw [Function.update_self, Function.update_self, hR₂d, hinc]
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases hk' : k = t
      · subst hk'; rw [Function.update_self, ht]
      · rw [Function.update_of_ne hk', hR₂o k hk hk']

/-- Convert the unary value `|a|` into its canonical binary digits on the empty register `d`
(bit symbols, least significant on top); `a` is kept through the empty `t₁`, `t₂` is a spare. -/
def sxBinConv (a d t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (sxBinInc d t₂)

/-- `sxBinConv`: `d` gains `(sxBits |a|).map bitSymbol`, in at most `16 |a| + 4` steps. -/
theorem sxBinConv_exec {a d t₁ t₂ : Fin T} (hreg : [a, d, t₁, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (hd : S.R d = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 16 * (S.R a).length + 4 ∧
      Exec body (sxBinConv a d t₁ t₂) (mk v S) m
        (mk v' { S with R := Function.update S.R d ((sxBits (S.R a).length).map bitSymbol) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨had, hat₁, hat₂⟩, ⟨hdt₁, hdt₂⟩, ht₁t₂⟩ := hreg
  let Ψ : ℕ → Regs T A := fun i => Function.update S.R d ((sxBits i).map bitSymbol)
  have hp : IterSpec body (sxBinInc d t₂) a t₁ Ψ
      (fun i => 4 * GrowingCounterData.carrySteps (sxBits i) + 1) (S.R a).length := by
    intro i _ v S' hS'
    have hd' : S'.R d = (sxBits i).map bitSymbol := by
      rw [hS' d had.symm hdt₁]; simp [Ψ]
    have ht₂' : S'.R t₂ = [] := by
      rw [hS' t₂ hat₂.symm ht₁t₂.symm]; simp [Ψ, Function.update_of_ne hdt₂.symm, ht₂]
    obtain ⟨v', hu, he⟩ := sxBinInc_exec body d t₂ hdt₂ (sxBits i) v S' hd' ht₂'
    refine ⟨v', _, _, hu, le_rfl, he, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne had]
    · simp [Function.update_of_ne hdt₁.symm]
    · intro k hka hkt
      by_cases hk : k = d
      · subst hk; simp [Ψ, sxBits_succ]
      · simp [Ψ, Function.update_of_ne hk, hS' k hka hkt]
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hat₁ hp 0 v S (by simp)
    (fun k _ _ => by
      by_cases hk : k = d
      · subst hk; simp [Ψ, hd, sxBits, GrowingCounterData.advance]
      · simp [Ψ, Function.update_of_ne hk])
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · have hs := sx_sum_carrySteps_le (S.R a).length
    simp only [Nat.zero_add, ht₁, List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    have : ∑ i ∈ Finset.range (S.R a).length,
        (4 * GrowingCounterData.carrySteps (sxBits i) + 1 + 3) =
        4 * ∑ i ∈ Finset.range (S.R a).length, GrowingCounterData.carrySteps (sxBits i) +
          4 * (S.R a).length := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
    omega
  · congr 2
    funext k
    by_cases hka : k = a
    · subst hka
      rw [ha', ht₁, List.reverse_nil, List.nil_append, Function.update_of_ne had]
    · by_cases hkt : k = t₁
      · subst hkt; rw [ht', Function.update_of_ne hdt₁.symm, ht₁]
      · rw [hΨ' k hka hkt, Nat.zero_add]

end Binary



/-! ### Masks with two-bit items -/

section Masks

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- One item: emit the bit `b₀`, then `K - 1` copies of `b₁`, scanning the `K` symbols of `KR`
through the empty `t₂` after moving its top symbol to `t₂`. -/
def sxItem (KR cnt w t₂ : Fin T) (b₀ b₁ : Bool) : Pr P T Q A U :=
  .seq (.act (emit cnt w b₀ .done)) (.seq (.act (popPush KR t₂)) (scanR KR t₂ (emit cnt w b₁)))

theorem sxItem_exec {KR t₂ cnt w : Fin T} (hreg : [KR, t₂, cnt, w].Nodup) {n X p : ℕ}
    {b₀ b₁ : Bool} (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p) (hK : 1 ≤ (R₀ KR).length) (ht₂ : R₀ t₂ = [])
    (hb : p < n → X.testBit p = b₀)
    (hz : ∀ q, p < q → q < p + (R₀ KR).length → q < n → X.testBit q = b₁) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (sxItem KR cnt w t₂ b₀ b₁) (mk v S) (4 * (R₀ KR).length + 4)
        (mk v' { S with R := maskRegs cnt w n X R₀ (p + (R₀ KR).length) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hKt, hKc, hKw⟩, ⟨htc, htw⟩, hcw⟩ := hreg'
  obtain ⟨x, rest, hx⟩ := List.exists_cons_of_length_pos hK
  obtain ⟨v₁, hu₁, hr₁⟩ := emit_run hcw b₀ (.done) v S
  have he₁ := Exec.act (body := body) (emit cnt w b₀ .done) (mk v S)
  rw [hr₁, run_done, hS, emitFx_maskRegs hcw hb] at he₁
  set M₁ := maskRegs cnt w n X R₀ (p + 1) with hM₁
  have hrun : (popPush KR t₂ : Act T Q A U).run (mk v₁ { S with R := M₁ }) =
      mk { v₁ with sym := some x }
        { S with R := Function.update (Function.update M₁ KR rest) t₂ [x] } := by
    have h1 : M₁ KR = x :: rest := by rw [hM₁, maskRegs_of_ne hKc hKw, hx]
    have h2 : M₁ t₂ = [] := by rw [hM₁, maskRegs_of_ne htc htw, ht₂]
    simp [popPush, Action.run, h1, h2, update_rt, Function.update_of_ne hKt.symm]
  have he₂ := Exec.act (body := body) (popPush KR t₂) (mk v₁ { S with R := M₁ })
  rw [hrun] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := scanR_exec body hKt (regFx_emit hcw b₁) (frame_emitFx hKc hKw b₁)
    (frame_emitFx htc htw b₁) { v₁ with sym := some x }
    { S with R := Function.update (Function.update M₁ KR rest) t₂ [x] }
  refine ⟨v₃, by rw [hu₃]; simpa using hu₁, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [Function.update_of_ne hKt, hx]; ring
  · congr 2
    dsimp only
    rw [Function.update_of_ne hKt, Function.update_self, Function.update_self,
      (frame_emitFx htc htw b₁).foldl, (frame_emitFx hKc hKw b₁).foldl, hM₁,
      foldl_emitFx hcw R₀ rest (p + 1) (fun q h1 h2 h3 => hz q (by omega) (by rw [hx]; simp; omega) h3)]
    funext k
    by_cases hk1 : k = KR
    · subst hk1; simp [maskRegs_of_ne hKc hKw, hx]
    · by_cases hk2 : k = t₂
      · subst hk2; simp [hk1, maskRegs_of_ne htc htw, ht₂]
      · simp only [Function.update_of_ne hk1, Function.update_of_ne hk2]
        rw [hx]; simp [Nat.add_assoc, Nat.add_comm 1]

/-- `|kR|` items at stride `K`, scanning `kR` through the empty `t₁`. -/
theorem sxItems_exec {kR KR cnt w t₁ t₂ : Fin T} (hreg : [kR, KR, cnt, w, t₁, t₂].Nodup)
    {n X p₀ K : ℕ} (b₀ b₁ : Bool) (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p₀) (hKl : (R₀ KR).length = K) (hK : 1 ≤ K)
    (ht₁ : R₀ t₁ = []) (ht₂ : R₀ t₂ = [])
    (hb : ∀ j < (R₀ kR).length, p₀ + K * j < n → X.testBit (p₀ + K * j) = b₀)
    (hz : ∀ j < (R₀ kR).length, ∀ s, 0 < s → s < K → p₀ + K * j + s < n →
      X.testBit (p₀ + K * j + s) = b₁) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ (R₀ kR).length * (4 * K + 9) + 4 ∧
      Exec body (scanP kR t₁ (sxItem KR cnt w t₂ b₀ b₁)) (mk v S) m
        (mk v' { S with R := maskRegs cnt w n X R₀ (p₀ + K * (R₀ kR).length) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hkK, hkc, hkw, hk1, hk2⟩, ⟨hKc, hKw, hK1, hK2⟩, ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ :=
    hreg'
  have hregI : [KR, t₂, cnt, w].Nodup := by
    simp [hKc, hKw, hK2, hc2.symm, hw2.symm, hcw]
  let Ψ : ℕ → Regs T A := fun j => maskRegs cnt w n X R₀ (p₀ + K * j)
  have hp : IterSpec body (sxItem KR cnt w t₂ b₀ b₁) kR t₁ Ψ (fun _ => 4 * K + 4)
      (R₀ kR).length := by
    intro j hj v' S' hS'
    have hc' : S'.R cnt = List.replicate (n - (p₀ + K * j)) tick :=
      (hS' cnt hkc.symm hc1).trans (maskRegs_cnt hcw _ _)
    have hw' : S'.R w = (binSyms (min (p₀ + K * j) n) X).reverse :=
      (hS' w hkw.symm hw1).trans (maskRegs_w _ _)
    have hKR : S'.R KR = R₀ KR := (hS' KR hkK.symm hK1).trans (maskRegs_of_ne hKc hKw _ _)
    have ht₂' : S'.R t₂ = [] :=
      (hS' t₂ hk2.symm h12.symm).trans ((maskRegs_of_ne hc2.symm hw2.symm _ _).trans ht₂)
    obtain ⟨v'', hu, he⟩ := sxItem_exec body hregI (S'.R) v' S' (maskRegs_self hc' hw').symm
      (by rw [hKR, hKl]; exact hK) ht₂' (hb j hj)
      (fun q h1 h2 h3 => by
        rw [hKR, hKl] at h2
        have := hz j hj (q - (p₀ + K * j)) (by omega) (by omega) (by omega)
        rwa [show p₀ + K * j + (q - (p₀ + K * j)) = q by omega] at this)
    have hpos : p₀ + K * j + (S'.R KR).length = p₀ + K * (j + 1) := by
      rw [hKR, hKl, Nat.mul_succ, Nat.add_assoc]
    rw [hpos] at he
    refine ⟨v'', _, _, hu, le_of_eq (by rw [hKR, hKl]), he, maskRegs_of_ne hkc hkw _ _,
      maskRegs_of_ne hc1.symm hw1.symm _ _, fun k hka hkt => ?_⟩
    exact maskRegs_congr _ fun h1 h2 => by
      rw [hS' k hka hkt]; exact maskRegs_of_ne h1 h2 _ _
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hk1 hp 0 v S
    (by rw [hS, maskRegs_of_ne hkc hkw]; simp)
    (fun k hka hkt => by rw [hS]; simp [Ψ])
  have hSk : S.R kR = R₀ kR := by rw [hS, maskRegs_of_ne hkc hkw]
  have hSt : S.R t₁ = [] := by rw [hS, maskRegs_of_ne hc1.symm hw1.symm, ht₁]
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hSk, hSt,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    nlinarith
  · congr 2
    funext k
    by_cases hka : k = kR
    · subst hka; rw [ha', hSt, maskRegs_of_ne hkc hkw, hSk]; rfl
    · by_cases hkt : k = t₁
      · subst hkt; rw [ht', maskRegs_of_ne hc1.symm hw1.symm, ht₁]
      · rw [hΨ' k hka hkt, hSk]; simp [Ψ]

/-- The two-bit mask builder. Registers: unary inputs `nR` (`n`), `oR` (`o`), `KR` (`K ≥ 1`),
`kR` (`N`); output `z`; empty spares `cnt`, `w`, `t₁`, `t₂`. Positions: `o` zeros; `N` items,
each the bit `b₀` and `K - 1` copies of `b₁`; `n` zeros of padding (positions past `n` are
dropped); `w` moved onto `z`. -/
def sxMask (nR oR KR kR z cnt w t₁ t₂ : Fin T) (b₀ b₁ : Bool) : Pr P T Q A U :=
  .seq (ucopy nR cnt t₁)
    (.seq (scanR oR t₁ (emit cnt w false))
      (.seq (scanP kR t₁ (sxItem KR cnt w t₂ b₀ b₁))
        (.seq (scanR nR t₁ (emit cnt w false)) (moveR w z id))))

/-- `sxMask`: `z` gains `binSyms n X` on top for every `X` whose low `n` bits follow the item
pattern; every other register ends as it started. -/
theorem sxMask_exec {nR oR KR kR z cnt w t₁ t₂ : Fin T}
    (hreg : [nR, oR, KR, kR, z, cnt, w, t₁, t₂].Nodup) (b₀ b₁ : Bool)
    {n o K N X : ℕ} (v : HS T Q A U) (S : Stacks T A) (hn : (S.R nR).length = n)
    (ho : (S.R oR).length = o) (hKl : (S.R KR).length = K) (hkl : (S.R kR).length = N)
    (hK : 1 ≤ K) (hc : S.R cnt = []) (hw : S.R w = []) (ht₁ : S.R t₁ = [])
    (ht₂ : S.R t₂ = [])
    (hX₁ : ∀ q < o, q < n → X.testBit q = false)
    (hX₂ : ∀ i < N, o + K * i < n → X.testBit (o + K * i) = b₀)
    (hX₃ : ∀ i < N, ∀ s, 0 < s → s < K → o + K * i + s < n → X.testBit (o + K * i + s) = b₁)
    (hX₄ : ∀ q, o + K * N ≤ q → q < n → X.testBit q = false) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 10 * n + 4 * o + N * (4 * K + 9) + 18 ∧
      Exec body (sxMask nR oR KR kR z cnt w t₁ t₂ b₀ b₁) (mk v S) m
        (mk v' { S with R := Function.update S.R z (binSyms n X ++ S.R z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hno, hnK, hnk, hnz, hnc, hnw, hn1, hn2⟩, ⟨hoK, hok, hoz, hoc, how, ho1, ho2⟩,
    ⟨hKk, hKz, hKc, hKw, hK1, hK2⟩, ⟨hkz, hkc, hkw, hk1, hk2⟩, ⟨hzc, hzw, hz1, hz2⟩,
    ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hnc hn1 hc1 v S ht₁
  rw [maskRegs_start (X := X) hcw S.R hc hw, hn] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := scanEmit_exec body (a := oR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [ho1, hoc, how, hc1.symm, hw1.symm, hcw])
    false S.R v₁ { S with R := maskRegs cnt w n X S.R 0 } rfl ht₁
    (fun q _ h2 h3 => hX₁ q (by rw [ho] at h2; omega) h3)
  rw [ho, Nat.zero_add] at he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := sxItems_exec body (kR := kR) (KR := KR) (cnt := cnt)
    (w := w) (t₁ := t₁) (t₂ := t₂)
    (by simp [hKk.symm, hkc, hkw, hk1, hk2, hKc, hKw, hK1, hK2, hcw, hc1, hc2, hw1, hw2, h12])
    b₀ b₁ S.R v₂ { S with R := maskRegs cnt w n X S.R o } rfl hKl hK ht₁ ht₂
    (fun j hj hlt => hX₂ j (by rw [← hkl]; exact hj) hlt)
    (fun j hj s hs hsK hlt => hX₃ j (by rw [← hkl]; exact hj) s hs hsK hlt)
  rw [hkl] at he₃ hm₃
  obtain ⟨v₄, hu₄, he₄⟩ := scanEmit_exec body (a := nR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [hn1, hnc, hnw, hc1.symm, hw1.symm, hcw])
    false S.R v₃ { S with R := maskRegs cnt w n X S.R (o + K * N) } rfl ht₁
    (fun q h1 _ h3 => hX₄ q h1 h3)
  rw [hn] at he₄
  obtain ⟨v₅, hu₅, he₅⟩ := maskFinish_exec body hzc hzw hcw (p := o + K * N + n)
    (by omega) S.R hc hw v₄ { S with R := maskRegs cnt w n X S.R (o + K * N + n) } rfl
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  rw [hn, ho] at *
  omega

end Masks

/-! ### Bit lists -/

section BitLists

variable {A : ℕ}

/-- A binary numeral split into a low part of `a` bits and a high part of `b` zero bits. -/
lemma sx_binSyms_append_zero {a b X Y : ℕ} (hlo : ∀ t < a, X.testBit t = Y.testBit t)
    (hhi : ∀ t, a ≤ t → t < a + b → Y.testBit t = false) :
    (binSyms a X ++ binSyms b 0 : List (Fin (A + 4))) = binSyms (a + b) Y := by
  apply List.ext_getElem (by simp)
  intro t h1 h2
  simp only [binSyms, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  split_ifs with h
  · rw [hlo t h]
  · simp only [Nat.zero_testBit]
    rw [hhi t (by omega) (by simp at h2; omega)]

end BitLists



/-! ### Slot order -/

section Order

/-- The slot index of each name: `x = 0`, `y = 1`, `z = 2`. -/
def sxSlot (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

/-- The physical order of the names by significance: physical chunk slot `0` holds the name with
the largest slot index, slot `2` the smallest. -/
def sxSigma (x y z : ℕ) : Equiv.Perm (Fin 3) :=
  if y < x ∧ z < y then 1
  else if z < x ∧ y < z then Equiv.swap 1 2
  else if x < y ∧ z < x then Equiv.swap 0 1
  else if z < y ∧ x < z then Equiv.swap 0 1 * Equiv.swap 1 2
  else if x < z ∧ y < x then Equiv.swap 1 2 * Equiv.swap 0 1
  else Equiv.swap 0 2

/-- The slot index of the name in physical slot `p`. -/
def sxPos (x y z : ℕ) (p : Fin 3) : ℕ := sxSlot x y z (sxSigma x y z p)

lemma sxPos_lt {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    sxPos x y z 2 < sxPos x y z 1 ∧ sxPos x y z 1 < sxPos x y z 0 := by
  unfold sxPos sxSigma
  split_ifs <;> simp [sxSlot, Equiv.swap_apply_of_ne_of_ne, Equiv.Perm.mul_apply] <;> omega

lemma sxPos_symm (x y z : ℕ) (q : Fin 3) :
    sxPos x y z ((sxSigma x y z).symm q) = sxSlot x y z q := by
  simp [sxPos]

end Order

/-! ### Bits of a replaced field -/

section Bits

/-- Replacing the `L`-bit field at bit `P` of `j` by `c'`. -/
lemma sx_testBit_replace (j P L c' t : ℕ) (hc' : c' < 2 ^ L) :
    (j % 2 ^ P + 2 ^ P * (c' + 2 ^ L * (j / 2 ^ (P + L)))).testBit t =
      if P ≤ t ∧ t < P + L then c'.testBit (t - P) else j.testBit t := by
  have hlo : j % 2 ^ P < 2 ^ P := Nat.mod_lt _ (by positivity)
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo, Nat.add_comm c',
    Nat.testBit_two_pow_mul_add _ hc']
  by_cases h1 : t < P
  · simp [h1, Nat.testBit_mod_two_pow]
  · by_cases h2 : t - P < L
    · simp [h1, h2, show P ≤ t ∧ t < P + L by omega]
    · simp only [h1, h2, ↓reduceIte, Nat.testBit_div_two_pow]
      rw [ite_eq_right (by omega)]
      congr 1; omega

/-- A number as its low part, an `L`-bit field at `P`, and its high part. -/
lemma sx_split_field (j P L : ℕ) :
    j = j % 2 ^ P + 2 ^ P * ((j / 2 ^ P) % 2 ^ L + 2 ^ L * (j / 2 ^ (P + L))) := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div, Nat.mod_add_div]

lemma sx_testBit_field (j P L i : ℕ) (hi : i < L) :
    ((j / 2 ^ P) % 2 ^ L).testBit i = j.testBit (P + i) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hi, Nat.add_comm]

lemma sx_testBit_addrNum {n : ℕ} (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a t : ℕ) (ht : t < n) :
    (addrNum σ a).testBit t = decide (σ (addrBits n a) ⟨t, ht⟩ = 1) := by
  have h := congrFun (IntegerMultBounds.MathlibTM2.Layer.addrBits_addrNum σ a) ⟨t, ht⟩
  simp only [addrBits] at h
  cases hb : (addrNum σ a).testBit t
  · rw [hb] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [← h]; decide
  · rw [hb] at h; simp only [↓reduceIte] at h
    rw [← h]; decide

end Bits

/-! ### The rectangle of a slot triple -/

section Rect

variable (a₀ L n : ℕ) (x y z : ℕ)

/-- The low field: the address bits below the lowest of the three slots. -/
def sxN3 : ℕ := a₀ + sxPos x y z 2 * L
/-- The gap between the lowest and the middle slot. -/
def sxN2 : ℕ := (sxPos x y z 1 - sxPos x y z 2 - 1) * L
/-- The gap between the middle and the highest slot. -/
def sxN1 : ℕ := (sxPos x y z 0 - sxPos x y z 1 - 1) * L
/-- The address bits above the highest slot. -/
def sxN0 : ℕ := n - (a₀ + (sxPos x y z 0 + 1) * L)

variable {a₀ L n x y z}

lemma sx_fieldOff_idxLen (n₀ n₁ n₂ n₃ L rb : ℕ) :
    fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) 1 = n₃ ∧
      fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) 3 = n₃ + L + n₂ ∧
      fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) 5 = n₃ + L + n₂ + L + n₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldOff, Finset.sum_filter, Fin.sum_univ_succ, idxLen] <;> ring

/-- The field of physical slot `p` starts at the bit `a₀ + (slot index) L`. -/
lemma fieldOff_slotF_sx (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (rb : ℕ) (p : Fin 3) :
    fieldOff (idxLen (sxN0 a₀ L n x y z) (sxN1 L x y z) (sxN2 L x y z) (sxN3 a₀ L x y z) L rb)
      (slotF p) = a₀ + sxPos x y z p * L := by
  obtain ⟨h1, h3, h5⟩ := sx_fieldOff_idxLen (sxN0 a₀ L n x y z) (sxN1 L x y z) (sxN2 L x y z)
    (sxN3 a₀ L x y z) L rb
  obtain ⟨hlo, hhi⟩ := sxPos_lt hxy hxz hyz
  obtain ⟨d1, hd1⟩ : ∃ d, sxPos x y z 1 = sxPos x y z 2 + 1 + d := ⟨_, (Nat.add_sub_of_le hlo).symm⟩
  obtain ⟨d0, hd0⟩ : ∃ d, sxPos x y z 0 = sxPos x y z 1 + 1 + d := ⟨_, (Nat.add_sub_of_le hhi).symm⟩
  have e2 : sxN2 L x y z = d1 * L := by simp only [sxN2]; congr 1; omega
  have e1 : sxN1 L x y z = d0 * L := by simp only [sxN1]; congr 1; omega
  fin_cases p
  · show fieldOff _ 5 = _
    rw [h5, e2, e1]
    simp only [sxN3, Fin.zero_eta]
    rw [hd0, hd1]; ring
  · show fieldOff _ 3 = _
    rw [h3, e2]
    simp only [sxN3]
    show _ = a₀ + sxPos x y z 1 * L
    rw [hd1]; ring
  · show fieldOff _ 1 = _
    rw [h1]; rfl

/-- The fields sum to the address width. -/
lemma sx_sum (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfit : a₀ + (sxPos x y z 0 + 1) * L ≤ n) :
    sxN3 a₀ L x y z + L + sxN2 L x y z + L + sxN1 L x y z + L + sxN0 a₀ L n x y z = n := by
  obtain ⟨hlo, hhi⟩ := sxPos_lt hxy hxz hyz
  simp only [sxN3, sxN2, sxN1, sxN0]
  have e1 : sxPos x y z 1 = sxPos x y z 2 + 1 + (sxPos x y z 1 - sxPos x y z 2 - 1) := by omega
  have e0 : sxPos x y z 0 = sxPos x y z 1 + 1 + (sxPos x y z 0 - sxPos x y z 1 - 1) := by omega
  set d1 := sxPos x y z 1 - sxPos x y z 2 - 1
  set d0 := sxPos x y z 0 - sxPos x y z 1 - 1
  rw [e0, e1] at hfit ⊢
  have : a₀ + sxPos x y z 2 * L + L + d1 * L + L + d0 * L + L =
      a₀ + (sxPos x y z 2 + 1 + d1 + 1 + d0 + 1) * L := by ring
  omega

end Rect

/-! ### The slot XOR on addresses -/

section SlotMap

open IntegerMultBounds.MathlibTM2.Layer (m)

/-- In every column, add the bit of slot `x` to slot `y`. -/
def sxXorCol (x y : Fin m) (a : IntegerMultBounds.Networks.BinaryWalsh.Address m) :
    IntegerMultBounds.Networks.BinaryWalsh.Address m :=
  a + Pi.single y (a x)

variable {n k : ℕ} (e : Fin (m * k) → Fin n)

/-- The address map of the slot XOR: column `c` of slot `y` gains column `c` of slot `x`. -/
noncomputable def sxMap (x y : Fin m) (b : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  merge e b (ofCols fun c => sxXorCol x y (colBits e c b))

lemma sx_pullM_xorCol {R r : ℕ} (x y : Fin m) (Z : ZArr (Fin R × Fin r) n) :
    pullM e (sxXorCol x y) Z = pullAddr (sxMap e x y) Z := rfl

lemma sx_ofCols_bitIdx {h k : ℕ} (X : IntegerMultBounds.Networks.BinaryColumns.Address h k)
    (j : Fin h) (c : Fin k) : ofCols X (bitIdx j c) = X c j := by
  have := congrFun (congrFun (IntegerMultBounds.MathlibTM2.Layer.toCols_ofCols X) c) j
  simpa [toCols] using this

variable {e}

lemma sxMap_apply_y (he : Function.Injective e) (x y : Fin m) (b : Fin n → ZMod 2) (c : Fin k) :
    sxMap e x y b (e (bitIdx y c)) = b (e (bitIdx y c)) + b (e (bitIdx x c)) := by
  simp only [sxMap, IntegerMultBounds.MathlibTM2.Layer.merge_apply_of_inj he, sx_ofCols_bitIdx, sxXorCol, Pi.add_apply,
    Pi.single_eq_same, colBits]

lemma sxMap_apply_ne (he : Function.Injective e) (x y : Fin m) (b : Fin n → ZMod 2) (t : Fin n)
    (ht : ∀ c : Fin k, e (bitIdx y c) ≠ t) : sxMap e x y b t = b t := by
  by_cases h : ∃ i, e i = t
  · obtain ⟨i, rfl⟩ := h
    obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective i
    have hj : j ≠ y := fun hj => ht c (by rw [← hj]; rfl)
    rw [sxMap, IntegerMultBounds.MathlibTM2.Layer.merge_apply_of_inj he]
    show ofCols _ (bitIdx j c) = _
    rw [sx_ofCols_bitIdx]
    simp only [sxXorCol, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, colBits]
    rfl
  · simp only [sxMap, IntegerMultBounds.MathlibTM2.Layer.merge, h, dite_false]

end SlotMap

/-! ### The slot XOR on record ranks -/

section Identity

open IntegerMultBounds.MathlibTM2.Layer (m)

variable {N₀ N₁ N₂ N₃ L : ℕ}

lemma sx_xorSel_apply_one (K ρ f : ℕ) (v : Tri L) :
    ((xorSel L K ρ f v 1 : Fin (2 ^ L)) : ℕ) = (v 1 : ℕ) ^^^ ((v 0 : ℕ) &&& selMask K ρ f) := by
  show ((xorMask L (selMask K ρ f) v 1 : Fin (2 ^ L)) : ℕ) = _
  simp [xorMask]

lemma sx_xorSel_apply_ne (K ρ f : ℕ) (v : Tri L) (q : Fin 3) (hq : q ≠ 1) :
    xorSel L K ρ f v q = v q := by
  show xorMask L (selMask K ρ f) v q = _
  simp [xorMask, Function.update_of_ne hq]

lemma sx_xorSel_symm (K ρ f : ℕ) : (xorSel L K ρ f).symm = xorSel L K ρ f := rfl

lemma sx_addrPerm_symm (σ : Equiv.Perm (Fin 3)) (Pm : Equiv.Perm (Tri L)) :
    (addrPerm N₀ N₁ N₂ N₃ L σ Pm).symm = addrPerm N₀ N₁ N₂ N₃ L σ Pm.symm := by
  ext j
  simp [addrPerm, liftA]

/-- The selected XOR on ranks: the rank moves by the change of the `y` field times its weight. -/
lemma sx_xorSel_enc (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    (enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (xorSel L K ρ f) a) : ℤ) =
      enc N₀ N₁ N₂ N₃ L σ a + slotW N₁ N₂ N₃ L (σ.symm 1) *
        ((((a.2 1 : ℕ) ^^^ ((a.2 0 : ℕ) &&& selMask K ρ f) : ℕ) : ℤ) - ((a.2 1 : ℕ) : ℤ)) := by
  obtain ⟨s, v⟩ := a
  rw [enc_val, enc_val]
  have hphys : phys L σ (xorSel L K ρ f v) =
      Function.update (phys L σ v) (σ.symm 1) (xorSel L K ρ f v 1) := by
    funext q
    by_cases hq : q = σ.symm 1
    · subst hq; simp [phys]
    · have hσq : σ q ≠ 1 := fun e => hq (by rw [← e, Equiv.symm_apply_apply])
      simp only [phys, Function.comp_apply, Function.update_of_ne hq]
      exact sx_xorSel_apply_ne K ρ f v (σ q) hσq
  show (rank N₀ N₁ N₂ N₃ L (s, phys L σ (xorSel L K ρ f v)) : ℤ) = _
  rw [hphys, rank_update, sx_xorSel_apply_one]
  simp [phys]

/-- The rank weights of the chunk slots are the powers of two at their field offsets. -/
lemma sx_slotW_pow {n₀ n₁ n₂ n₃ rb : ℕ} (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
    (p : Fin 3) : slotW N₁ N₂ N₃ L p = 2 ^ fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) (slotF p) := by
  obtain ⟨h1, h3, h5⟩ := sx_fieldOff_idxLen n₀ n₁ n₂ n₃ L rb
  subst hN₁ hN₂ hN₃
  fin_cases p
  · show _ = 2 ^ fieldOff _ 5
    simp [slotW, pow_add, h5]
  · show _ = 2 ^ fieldOff _ 3
    simp [slotW, pow_add, h3]
  · show _ = 2 ^ fieldOff _ 1
    simp [slotW, h1]

lemma sx_zmod2_ite_add (p q : Bool) :
    decide (((if p then 1 else 0 : ZMod 2) + (if q then 1 else 0)) = 1) = xor p q := by
  cases p <;> cases q <;> decide

lemma sx_decide_ite_one (p : Bool) : decide ((if p then 1 else 0 : ZMod 2) = 1) = p := by
  cases p <;> decide

variable {n k a₀ K ρ R rb : ℕ} {x y z : Fin m} {e : Fin (m * k) → Fin n}

/-- **The slot XOR on ranks.** With the rectangle of the slots `x, y, z` (fields `sxN3`, the three
slots, the gaps and the top bits with the rows), the packed target `xorSel` moves the record at
rank `2^n u + a` to the rank `2^n u + addrNum (sxMap e x y) a`. -/
theorem sx_addrPerm_xorSel (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hρ : ρ < K)
    (hLK : L = K * k) (hfit : a₀ + (sxPos x y z 0 + 1) * L ≤ n)
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (hR : R ≤ 2 ^ rb)
    (hN₀ : N₀ = R * 2 ^ sxN0 a₀ L n x y z) (hN₁ : N₁ = 2 ^ sxN1 L x y z)
    (hN₂ : N₂ = 2 ^ sxN2 L x y z) (hN₃ : N₃ = 2 ^ sxN3 a₀ L x y z)
    (j : Fin (rectSize N₀ N₁ N₂ N₃ L)) :
    (addrPerm N₀ N₁ N₂ N₃ L (sxSigma x y z) (xorSel L K ρ k) j : ℕ) =
      2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) := by
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  have hxz' : (x : ℕ) ≠ z := fun h => hxz (Fin.ext h)
  have hyz' : (y : ℕ) ≠ z := fun h => hyz (Fin.ext h)
  set σ := sxSigma x y z with hσ
  set n₀ := sxN0 a₀ L n x y z
  set n₁ := sxN1 L x y z
  set n₂ := sxN2 L x y z
  set n₃ := sxN3 a₀ L x y z
  have hK : 0 < K := by omega
  -- the field offsets of the names
  have hoff : ∀ q : Fin 3, fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) (slotF (σ.symm q)) =
      a₀ + sxSlot x y z q * L := fun q => by
    rw [fieldOff_slotF_sx hxy' hxz' hyz', hσ, sxPos_symm]
  have hP1 : fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) (slotF (σ.symm 1)) = a₀ + y * L := hoff 1
  have hP0 : fieldOff (idxLen n₀ n₁ n₂ n₃ L rb) (slotF (σ.symm 0)) = a₀ + x * L := hoff 0
  set P := a₀ + (y : ℕ) * L with hP
  set Px := a₀ + (x : ℕ) * L with hPx
  -- the slots fit below `n`
  have hpos : ∀ q, sxSlot x y z q ≤ sxPos x y z 0 := by
    intro q
    obtain ⟨h1, h2⟩ := sxPos_lt hxy' hxz' hyz'
    have : sxSlot x y z q = sxPos x y z (σ.symm q) := (sxPos_symm x y z q).symm
    rw [this]
    generalize σ.symm q = p
    fin_cases p <;> simp <;> omega
  have hPfit : P + L ≤ n := by
    have := hpos 1
    have h2 : (y : ℕ) * L + L ≤ (sxPos x y z 0 + 1) * L := by
      rw [Nat.add_mul, one_mul]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _
    omega
  -- the record address of `j`
  obtain ⟨q, hq⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective j
  have hjq : (j : ℕ) = enc N₀ N₁ N₂ N₃ L σ q := by rw [hq]
  have hdig : ∀ q' : Fin 3, ((q.2 q' : Fin (2 ^ L)) : ℕ) =
      ((j : ℕ) / 2 ^ (a₀ + sxSlot x y z q' * L)) % 2 ^ L := by
    intro q'
    have := digit_enc_name (n₀ := n₀) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (rb := rb) hN₀ hR hN₁ hN₂
      hN₃ σ q q'
    rw [← this, ← hq, digit, hoff q', idxLen_slotF]
  have hcy : ((q.2 1 : Fin (2 ^ L)) : ℕ) = ((j : ℕ) / 2 ^ P) % 2 ^ L := hdig 1
  have hcx : ((q.2 0 : Fin (2 ^ L)) : ℕ) = ((j : ℕ) / 2 ^ Px) % 2 ^ L := hdig 0
  have hcylt : ((j : ℕ) / 2 ^ P) % 2 ^ L < 2 ^ L := Nat.mod_lt _ (by positivity)
  have hcxlt : ((j : ℕ) / 2 ^ Px) % 2 ^ L < 2 ^ L := Nat.mod_lt _ (by positivity)
  have hperm : (addrPerm N₀ N₁ N₂ N₃ L σ (xorSel L K ρ k) j : ℕ) =
      enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (xorSel L K ρ k) q) := by
    rw [← hq, addrPerm_enc]
  have h1 := sx_xorSel_enc (N₀ := N₀) K ρ k σ q
  rw [sx_slotW_pow (n₀ := n₀) (rb := rb) hN₁ hN₂ hN₃, hP1, hcy, hcx, ← hjq] at h1
  have h2 := sx_split_field (j : ℕ) P L
  set cy := ((j : ℕ) / 2 ^ P) % 2 ^ L
  set cx := ((j : ℕ) / 2 ^ Px) % 2 ^ L
  set wv := cy ^^^ (cx &&& selMask K ρ k) with hwv
  have hwlt : wv < 2 ^ L := Nat.xor_lt_two_pow hcylt (lt_of_le_of_lt Nat.and_le_left hcxlt)
  -- the new rank
  have hnew : (addrPerm N₀ N₁ N₂ N₃ L σ (xorSel L K ρ k) j : ℕ) =
      (j : ℕ) % 2 ^ P + 2 ^ P * (wv + 2 ^ L * ((j : ℕ) / 2 ^ (P + L))) := by
    rw [hperm]
    have h3 : ((enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (xorSel L K ρ k) q) : ℕ) : ℤ) =
        (((j : ℕ) % 2 ^ P + 2 ^ P * (wv + 2 ^ L * ((j : ℕ) / 2 ^ (P + L))) : ℕ) : ℤ) := by
      rw [h1]
      have h2' : ((j : ℕ) : ℤ) = (((j : ℕ) % 2 ^ P + 2 ^ P * (cy + 2 ^ L * ((j : ℕ) / 2 ^ (P + L))) :
          ℕ) : ℤ) := by exact_mod_cast h2
      rw [h2']
      push_cast
      ring
    exact_mod_cast h3
  rw [hnew]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [sx_testBit_replace _ _ _ _ _ hwlt,
    Nat.testBit_two_pow_mul_add _ (IntegerMultBounds.MathlibTM2.Layer.addrNum_lt _ _)]
  by_cases htn : t < n
  · rw [ite_eq_left htn, sx_testBit_addrNum _ _ _ htn]
    have hbit : ∀ t' (h : t' < n), addrBits n ((j : ℕ) % 2 ^ n) ⟨t', h⟩ =
        if (j : ℕ).testBit t' then 1 else 0 := fun t' h => by
      simp [addrBits, Nat.testBit_mod_two_pow, h]
    have hey : ∀ c : Fin k, ((e (bitIdx y c) : Fin n) : ℕ) = P + (ρ + c * K) := fun c => by
      rw [he, bitIdx, finProdFinEquiv_apply_val, hP, hLK]; ring
    have hex : ∀ c : Fin k, ((e (bitIdx x c) : Fin n) : ℕ) = Px + (ρ + c * K) := fun c => by
      rw [he, bitIdx, finProdFinEquiv_apply_val, hPx, hLK]; ring
    by_cases hin : P ≤ t ∧ t < P + L
    · rw [ite_eq_left hin]
      set i := t - P with hi
      have hiL : i < L := by omega
      have htP : t = P + i := by omega
      rw [hwv, Nat.testBit_xor, Nat.testBit_and, sx_testBit_field _ _ _ _ hiL,
        sx_testBit_field _ _ _ _ hiL]
      by_cases hsel : IsSel K ρ k i
      · obtain ⟨c, hc, hci⟩ := hsel
        have hsel' : (selMask K ρ k).testBit i = true := (testBit_selMask K ρ k i).2 ⟨c, hc, hci⟩
        rw [hsel', Bool.and_true]
        have hyc : e (bitIdx y ⟨c, hc⟩) = ⟨t, htn⟩ := Fin.ext (by rw [hey]; simp [htP, hci])
        rw [← hyc, sxMap_apply_y (fun i i' h => by
            have := congrArg Fin.val h; rw [he, he] at this
            exact Fin.ext (Nat.eq_of_mul_eq_mul_left hK (by omega))) x y]
        have hx1 : (e (bitIdx x ⟨c, hc⟩) : ℕ) < n := (e _).isLt
        rw [show e (bitIdx y ⟨c, hc⟩) = ⟨_, (e (bitIdx y ⟨c, hc⟩)).isLt⟩ from rfl,
          show e (bitIdx x ⟨c, hc⟩) = ⟨_, hx1⟩ from rfl, hbit, hbit, sx_zmod2_ite_add, hey, hex]
        simp [hci]
      · have hsel' : (selMask K ρ k).testBit i = false := selMask_false K ρ k hsel
        rw [hsel', Bool.and_false, Bool.xor_false]
        rw [sxMap_apply_ne (fun i i' h => by
            have := congrArg Fin.val h; rw [he, he] at this
            exact Fin.ext (Nat.eq_of_mul_eq_mul_left hK (by omega))) x y _ _ (fun c hc => by
          apply hsel
          refine ⟨c, c.isLt, ?_⟩
          have := congrArg Fin.val hc
          rw [hey] at this
          simp at this
          omega), hbit, sx_decide_ite_one, htP]
    · rw [ite_eq_right hin]
      rw [sxMap_apply_ne (fun i i' h => by
          have := congrArg Fin.val h; rw [he, he] at this
          exact Fin.ext (Nat.eq_of_mul_eq_mul_left hK (by omega))) x y _ _ (fun c hc => by
        apply hin
        have := congrArg Fin.val hc
        rw [hey] at this
        simp at this
        have hcK : (c : ℕ) * K + K ≤ L := by
          rw [hLK, ← Nat.succ_mul, Nat.mul_comm]
          exact Nat.mul_le_mul_left _ c.isLt
        omega), hbit, sx_decide_ite_one]
  · rw [ite_eq_right htn, ite_eq_right (by omega), Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

lemma sx_flatMap_flatten {α β : Type} (f : α → List β) (l : List (List α)) :
    l.flatten.flatMap f = (l.map (fun x => x.flatMap f)).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_append, ih]

/-- The stream of an array is the concatenation of its records. -/
lemma sx_encZ_eq_flatten {A w R r : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    encZ A w Z = ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w)).flatten := by
  rw [encZ, coeffList, sx_flatMap_flatten]
  rfl

/-- The rectangle of the slot triple has `R 2^n` records. -/
lemma sx_rectSize (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfit : a₀ + (sxPos x y z 0 + 1) * L ≤ n) :
    rectSize (R * 2 ^ sxN0 a₀ L n x y z) (2 ^ sxN1 L x y z) (2 ^ sxN2 L x y z)
      (2 ^ sxN3 a₀ L x y z) L = R * 2 ^ n := by
  have hs := sx_sum (fun h => hxy (Fin.ext h)) (fun h => hxz (Fin.ext h))
    (fun h => hyz (Fin.ext h)) hfit
  have h : rectSize (R * 2 ^ sxN0 a₀ L n x y z) (2 ^ sxN1 L x y z) (2 ^ sxN2 L x y z)
      (2 ^ sxN3 a₀ L x y z) L = R * 2 ^ (sxN3 a₀ L x y z + L + sxN2 L x y z + L + sxN1 L x y z +
        L + sxN0 a₀ L n x y z) := by
    simp only [rectSize, pow_add]; ring
  rw [h, hs]

/-- **The slot XOR on the stream.** Moving the records by the packed target `xorSel` turns the
records of `Z` into the records of `pullM e (sxXorCol x y) Z`. -/
theorem sx_moveRecs_xorSel {A w r : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hρ : ρ < K)
    (hLK : L = K * k) (hfit : a₀ + (sxPos x y z 0 + 1) * L ≤ n)
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (hR : R ≤ 2 ^ rb)
    (hN₀ : N₀ = R * 2 ^ sxN0 a₀ L n x y z) (hN₁ : N₁ = 2 ^ sxN1 L x y z)
    (hN₂ : N₂ = 2 ^ sxN2 L x y z) (hN₃ : N₃ = 2 ^ sxN3 a₀ L x y z)
    (Z : ZArr (Fin R × Fin r) n) :
    (moveRecs (addrPerm N₀ N₁ N₂ N₃ L (sxSigma x y z) (xorSel L K ρ k))
        ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w))).flatten =
      encZ A w (pullM e (sxXorCol x y) Z) := by
  have hM : rectSize N₀ N₁ N₂ N₃ L = R * 2 ^ n := by
    rw [hN₀, hN₁, hN₂, hN₃]; exact sx_rectSize hxy hxz hyz hfit
  rw [sx_encZ_eq_flatten, sx_pullM_xorCol]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp [length_moveRecs, IntegerMultBounds.MathlibTM2.Layer.length_recList, hM]
  intro j h1 h2
  have hj : j < rectSize N₀ N₁ N₂ N₃ L := by simpa [length_moveRecs] using h1
  have hjR : j < R * 2 ^ n := hM ▸ hj
  have hu : j / 2 ^ n < R := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; linarith [hjR]
  have ha : j % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hdec : 2 ^ n * (j / 2 ^ n) + j % 2 ^ n = j := Nat.div_add_mod j (2 ^ n)
  have hperm := sx_addrPerm_xorSel hxy hxz hyz hρ hLK hfit he hR hN₀ hN₁ hN₂ hN₃ ⟨j, hj⟩
  have hlt : 2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) < (recList w Z).length := by
    rw [IntegerMultBounds.MathlibTM2.Layer.length_recList]
    have := IntegerMultBounds.MathlibTM2.Layer.addrNum_lt (sxMap e x y) (j % 2 ^ n)
    have h3 : 2 ^ n * (j / 2 ^ n + 1) ≤ 2 ^ n * R := Nat.mul_le_mul_left _ hu
    rw [Nat.mul_succ] at h3
    rw [Nat.mul_comm R]; omega
  simp only [moveRecs, List.getElem_ofFn, List.getElem_map]
  have hpermS : ((addrPerm N₀ N₁ N₂ N₃ L (sxSigma x y z) (xorSel L K ρ k)).symm ⟨j, hj⟩ : ℕ) =
      2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) := by
    have hsymm : (addrPerm N₀ N₁ N₂ N₃ L (sxSigma x y z) (xorSel L K ρ k)).symm ⟨j, hj⟩ =
        addrPerm N₀ N₁ N₂ N₃ L (sxSigma x y z) (xorSel L K ρ k) ⟨j, hj⟩ := by
      rw [sx_addrPerm_symm, sx_xorSel_symm]
    rw [hsymm]; exact hperm
  have hlt' : 2 ^ n * (j / 2 ^ n) + addrNum (sxMap e x y) (j % 2 ^ n) <
      ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w)).length := by
    rw [List.length_map]; exact hlt
  rw [hpermS, List.getD_eq_getElem _ _ hlt', List.getElem_map]
  congr 1
  have := IntegerMultBounds.MathlibTM2.Layer.recList_pull (w := w) (sxMap e x y) Z (j / 2 ^ n) hu (j % 2 ^ n) ha
  simp only [hdec] at this
  rw [this]

end Identity

/-! ### Registers of the slot XOR -/

noncomputable section

/-- The registers of the slot-XOR machine. The first group is built by the setup stages:
the unary field lengths `n3, n2, n1, n0`, the row count in binary `rbin` and its bit count `rb`,
the field counter `cf`, the counters `ctrB` (record length), `ctrK` (key length), `ctrKB`
(keyed record length), `cnt` (record count), the binary numbers `bbin` (three keyed record
lengths) and `lbin` (slot width), the masks `msel`, `mgrd`, `mtop`, and the five header registers
of each of the three interchange banks `swp c` (one bank per pair of exchanged chunk slots). The
second group is empty at rest: scratch `sc`, the other registers of the banks, and the work
registers of the key pass
(`kacc ktmp kt`), the rotation pass (`rtmp rctmp rout rdst raux rsp`), the repair pass
(`pgR pbR pg pb ptmp pus`), the fix pass (`fr fq ftmp fus`) and the swap pass (`stmp`). -/
inductive SXReg where
  | n3 | n2 | n1 | n0 | rbin | rb
  | cf (j : Fin 8)
  | ctrB | ctrK | ctrKB | cnt | bbin | lbin | msel | mgrd | mtop
  | sc (i : Fin 6)
  | swp (c : Fin 3) (j : Fin (swapT 6))
  | kacc | ktmp | kt (i : Fin 3)
  | rtmp | rctmp | rout | rdst (d : Fin 2) | raux (d : Fin 2) | rsp (r : Fin 4)
  | pgR | pbR | pg | pb | ptmp | pus (r : Fin 4)
  | fr (i : Fin 4) | fq (i : Fin 4) | ftmp | fus (r : Fin 3)
  | stmp
  deriving DecidableEq, Fintype

end

/-- The unary parameter registers read by the slot XOR. -/
inductive SXPar where
  | K | ρ | a₀ | L | rows | n | rw
  deriving DecidableEq

/-- The data of one slot XOR: bit stride `K`, offsets `ρ` and `a₀`, slot width `L = K k`, row
count `R`, address width `n`, record length `rw`, and the static slots `x y z`. -/
structure SxD where
  a₀ : ℕ
  K : ℕ
  ρ : ℕ
  L : ℕ
  R : ℕ
  n : ℕ
  rw : ℕ
  k : ℕ
  x : ℕ
  y : ℕ
  z : ℕ

namespace SxD

variable (d : SxD)

def n3 : ℕ := sxN3 d.a₀ d.L d.x d.y d.z
def n2 : ℕ := sxN2 d.L d.x d.y d.z
def n1 : ℕ := sxN1 d.L d.x d.y d.z
def n0 : ℕ := sxN0 d.a₀ d.L d.n d.x d.y d.z
/-- The bits of the row field. -/
def rb : ℕ := (sxBits d.R).length
/-- The key length. -/
def kl : ℕ := d.n + d.rb
/-- The keyed record length. -/
def Bk : ℕ := d.rw + d.kl
/-- The record count. -/
def M : ℕ := d.R * 2 ^ d.n
def lo : ℕ := sxPos d.x d.y d.z 2
def mid : ℕ := sxPos d.x d.y d.z 1
def hi : ℕ := sxPos d.x d.y d.z 0
def σ : Equiv.Perm (Fin 3) := sxSigma d.x d.y d.z
def N₀ : ℕ := d.R * 2 ^ d.n0
def N₁ : ℕ := 2 ^ d.n1
def N₂ : ℕ := 2 ^ d.n2
def N₃ : ℕ := 2 ^ d.n3
/-- The field lengths of the record index. -/
def len : Fin 8 → ℕ := idxLen d.n0 d.n1 d.n2 d.n3 d.L d.rb
/-- The parameter values. -/
def par : SXPar → ℕ
  | .K => d.K | .ρ => d.ρ | .a₀ => d.a₀ | .L => d.L | .rows => d.R | .n => d.n | .rw => d.rw

end SxD

/-- The pair class of an exchange of chunk slots `a, b`, as in `swapDims`. -/
def sxCls (a b : Fin 3) : Fin 3 := if a ≠ 2 ∧ b ≠ 2 then 0 else if a ≠ 0 ∧ b ≠ 0 then 1 else 2

/-- The number of low zero bits of header `k` of bank `c`. -/
def sxHe (d : SxD) : Fin 3 → Fin 5 → ℕ
  | 0, 0 => d.n0 | 0, 1 => d.n1 | 0, 2 => d.n3 + d.L + d.n2
  | 1, 0 => d.n1 + d.L + d.n0 | 1, 1 => d.n2 | 1, 2 => d.n3
  | 2, 0 => d.n0 | 2, 1 => d.n1 + d.L + d.n2 | 2, 2 => d.n3
  | _, _ => 0

/-- The high bits of header `k`: the row count, `1`, three keyed record lengths, and `L`. -/
def sxHbits (d : SxD) : Fin 5 → List Bool
  | 0 => sxBits d.R | 1 => [true] | 2 => sxBits (3 * d.Bk) | _ => sxBits d.L

/-- The canonical binary counter of header `k` of bank `c`. -/
def sxHs (d : SxD) (c : Fin 3) (k : Fin 5) : List Bool :=
  List.replicate (sxHe d c k) false ++ sxHbits d k

/-- The setup stage building each register (`0`: empty at rest). -/
def sxStage : SXReg → ℕ
  | .n3 => 1 | .n2 => 2 | .n1 => 3 | .n0 => 4 | .rbin => 5 | .rb => 6
  | .cf j => 7 + j
  | .ctrB => 15 | .ctrK => 16 | .ctrKB => 17 | .cnt => 18 | .bbin => 19 | .lbin => 20
  | .msel => 21 | .mgrd => 22 | .mtop => 23
  | .swp c j => if j.val < 5 then 24 + 5 * c.val + j.val else 0
  | _ => 0

lemma sx_five_lt_swapT : 5 < swapT 6 := by
  unfold swapT IntegerMultBounds.Machine.BinaryInterchangeRun.bankCount; omega

/-- The register built by a setup stage. -/
def sxOfStage : ℕ → SXReg
  | 1 => .n3 | 2 => .n2 | 3 => .n1 | 4 => .n0 | 5 => .rbin | 6 => .rb
  | 7 => .cf 0 | 8 => .cf 1 | 9 => .cf 2 | 10 => .cf 3 | 11 => .cf 4 | 12 => .cf 5
  | 13 => .cf 6 | 14 => .cf 7
  | 15 => .ctrB | 16 => .ctrK | 17 => .ctrKB | 18 => .cnt | 19 => .bbin | 20 => .lbin
  | 21 => .msel | 22 => .mgrd | 23 => .mtop
  | s => if h : 24 ≤ s ∧ s ≤ 38 then
      .swp ⟨(s - 24) / 5, by omega⟩ ⟨(s - 24) % 5, by have := sx_five_lt_swapT; omega⟩
    else .stmp

lemma sxOfStage_stage (x : SXReg) (hx : sxStage x ≠ 0) : sxOfStage (sxStage x) = x := by
  cases x with
  | cf j => fin_cases j <;> rfl
  | swp c j =>
      simp only [sxStage] at hx ⊢
      split_ifs at hx ⊢ with hj
      · have hc := c.isLt
        have e1 : (24 + 5 * c.val + j.val - 24) / 5 = c.val := by omega
        have e2 : (24 + 5 * c.val + j.val - 24) % 5 = j.val := by omega
        rw [sxOfStage.eq_def]
        split
        all_goals first | omega | skip
        rw [dite_eq_left (by omega)]
        congr 1
        · exact Fin.ext e1
        · exact Fin.ext e2
      · exact absurd rfl hx
  | _ => first | rfl | exact absurd rfl hx

lemma sxStage_le (x : SXReg) : sxStage x ≤ 38 := by
  cases x with
  | cf j => have := j.isLt; simp only [sxStage]; omega
  | swp c j =>
      have := c.isLt; simp only [sxStage]; split_ifs <;> omega
  | _ => simp [sxStage]

lemma sxStage_inj {x y : SXReg} (h : sxStage x = sxStage y) (hx : sxStage x ≠ 0) : x = y := by
  rw [← sxOfStage_stage x hx, ← sxOfStage_stage y (h ▸ hx), h]

/-- The contents of the registers after the setup. -/
def sxBc (A : ℕ) (d : SxD) : SXReg → List (Fin (A + 4))
  | .n3 => List.replicate d.n3 tick
  | .n2 => List.replicate d.n2 tick
  | .n1 => List.replicate d.n1 tick
  | .n0 => List.replicate d.n0 tick
  | .rbin => (sxBits d.R).map bitSymbol
  | .rb => List.replicate d.rb tick
  | .cf j => binSyms (d.len j) 0
  | .ctrB => List.replicate d.rw tick
  | .ctrK => List.replicate d.kl tick
  | .ctrKB => List.replicate d.Bk tick
  | .cnt => List.replicate d.M tick
  | .bbin => (sxBits (3 * d.Bk)).map bitSymbol
  | .lbin => (sxBits d.L).map bitSymbol
  | .msel => binSyms d.L (selMask d.K d.ρ (d.k - 1))
  | .mgrd => binSyms d.L (guardMask d.K d.ρ (d.k - 1) d.L)
  | .mtop => binSyms d.L (2 ^ (d.ρ + (d.k - 1) * d.K))
  | .swp c j => if h : j.val < 5 then separator :: (sxHs d c ⟨j.val, h⟩).map bitSymbol else []
  | _ => []

lemma sxBc_zero (A : ℕ) (d : SxD) (x : SXReg) (hx : sxStage x = 0) : sxBc A d x = [] := by
  cases x with
  | swp c j =>
      simp only [sxStage] at hx
      split_ifs at hx with hj
      · omega
      · simp [sxBc, hj]
  | _ => first | rfl | (simp [sxStage] at hx)

/-! ### Register files during the setup -/

section Fill

variable {T A : ℕ} (ι : SXReg → Fin T)

/-- The register file after the first `s` setup stages, over the base file `R₀`. -/
noncomputable def sxFill (bc : SXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.extend ι (fun x => if sxStage x ≤ s then bc x else []) R₀

variable {ι}

lemma sxFill_ι (hι : Function.Injective ι) (bc : SXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) (x : SXReg) :
    sxFill ι bc s R₀ (ι x) = if sxStage x ≤ s then bc x else [] :=
  hι.extend_apply _ _ _

lemma sxFill_out (bc : SXReg → List (Fin (A + 4))) (s : ℕ) (R₀ : Fin T → List (Fin (A + 4)))
    {t : Fin T} (ht : ∀ x, ι x ≠ t) : sxFill ι bc s R₀ t = R₀ t :=
  Function.extend_apply' _ _ _ (by rintro ⟨x, rfl⟩; exact ht x rfl)

lemma sxFill_step (hι : Function.Injective ι) (bc : SXReg → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : SXReg} (hx : sxStage x = s + 1) :
    Function.update (sxFill ι bc s R₀) (ι x) (bc x) = sxFill ι bc (s + 1) R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [sxFill_ι hι]
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_left (by omega)]
    · rw [Function.update_of_ne (hι.ne hy), sxFill_ι hι]
      have : sxStage y ≠ s + 1 := fun h => hy (sxStage_inj (h.trans hx.symm) (by omega))
      by_cases h1 : sxStage y ≤ s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · simp only [not_exists] at ht
    rw [Function.update_of_ne (fun h => ht x h.symm), sxFill_out _ _ _ ht, sxFill_out _ _ _ ht]

lemma sxFill_unstep (hι : Function.Injective ι) (bc : SXReg → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : SXReg} (hx : sxStage x = s + 1) :
    Function.update (sxFill ι bc (s + 1) R₀) (ι x) [] = sxFill ι bc s R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [sxFill_ι hι]
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_right (by omega)]
    · rw [Function.update_of_ne (hι.ne hy), sxFill_ι hι]
      have : sxStage y ≠ s + 1 := fun h => hy (sxStage_inj (h.trans hx.symm) (by omega))
      by_cases h1 : sxStage y ≤ s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · simp only [not_exists] at ht
    rw [Function.update_of_ne (fun h => ht x h.symm), sxFill_out _ _ _ ht, sxFill_out _ _ _ ht]

lemma sxFill_zero (hι : Function.Injective ι) (bc : SXReg → List (Fin (A + 4)))
    (R₀ : Fin T → List (Fin (A + 4))) (h0 : ∀ x, R₀ (ι x) = [])
    (hbc : ∀ x, sxStage x = 0 → bc x = []) : sxFill ι bc 0 R₀ = R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [sxFill_ι hι, h0]
    split_ifs with h
    · exact hbc y (by omega)
    · rfl
  · simp only [not_exists] at ht
    rw [sxFill_out _ _ _ ht]

lemma sxFill_update (hι : Function.Injective ι) (bc : SXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) {t : Fin T} (ht : ∀ x, ι x ≠ t) (l : List (Fin (A + 4))) :
    Function.update (sxFill ι bc s R₀) t l = sxFill ι bc s (Function.update R₀ t l) := by
  funext t'
  by_cases h : ∃ y, ι y = t'
  · obtain ⟨y, rfl⟩ := h
    rw [Function.update_of_ne (ht y), sxFill_ι hι, sxFill_ι hι]
  · simp only [not_exists] at h
    rw [sxFill_out _ _ _ h]
    by_cases htt : t' = t
    · subst htt; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne htt, Function.update_of_ne htt, sxFill_out _ _ _ h]

end Fill

/-! ### Chains of programs -/

section Chain

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- A chain of programs `p (s + i)`, each taking the register file `F (s + i)` to
`F (s + i + 1)`. -/
theorem sx_chain_exec (F : ℕ → Fin T → List (Fin (A + 4))) (p : ℕ → Pr P T Q A U) (c : ℕ → ℕ) :
    ∀ (N s : ℕ), (∀ i < N, ∀ (v : HS T Q A U) (S : Stacks T A), S.R = F (s + i) →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c (s + i) ∧
        Exec body (p (s + i)) (mk v S) m (mk v' { S with R := F (s + i + 1) })) →
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = F s →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
        m ≤ ∑ i ∈ Finset.range N, c (s + i) + 1 ∧
        Exec body (Prog.seqList ((List.range N).map fun i => p (s + i))) (mk v S) m
          (mk v' { S with R := F (s + N) }) := by
  intro N
  induction N with
  | zero =>
      intro s _ v S hS
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      rw [run_done]
      congr 1
      cases S; simp_all
  | succ N ih =>
      intro s h v S hS
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h 0 (by omega) v S (by simpa using hS)
      obtain ⟨v', m', hu', hm', he'⟩ := ih (s + 1)
        (fun i hi v S hS => by
          obtain ⟨v'', m'', hu'', hm'', he''⟩ := h (i + 1) (by omega) v S
            (by rw [hS]; congr 1; omega)
          exact ⟨v'', m'', hu'', by rw [show s + 1 + i = s + (i + 1) by omega]; exact hm'',
            by rw [show s + 1 + i + 1 = s + (i + 1) + 1 by omega,
              show s + 1 + i = s + (i + 1) by omega]; exact he''⟩)
        v₁ { S with R := F (s + 0 + 1) } (by simp)
      have hlist : (List.range (N + 1)).map (fun i => p (s + i)) =
          p s :: (List.range N).map (fun i => p (s + 1 + i)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]
      refine ⟨v', m₁ + m', hu'.trans hu₁, ?_, ?_⟩
      · rw [Finset.sum_range_succ']
        have : ∑ i ∈ Finset.range N, c (s + (i + 1)) = ∑ i ∈ Finset.range N, c (s + 1 + i) :=
          Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
        simp only [Nat.add_zero] at hm₁ ⊢
        omega
      · rw [hlist]
        refine Exec.cast (Exec.seq (by simpa using he₁) he') rfl ?_
        congr 2
        rw [show s + 1 + N = s + (N + 1) by omega]

end Chain


/-! ### Sequencing register programs -/

section Then

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable {p : Pr P T Q A U} {s : IntegerMultBounds.MathlibTM2.Stack.Store (HΓ (T := T) A) (HS T Q A U)} {m : ℕ}
  {v₁ : HS T Q A U} {S₁ : Stacks T A}

lemma sx_then_ucopy (he : Exec body p s m (mk v₁ S₁)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ht : S₁.R t = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (ucopy a b t)) s (m + (4 * (S₁.R a).length + 4))
        (mk v₂ { S₁ with
          R := Function.update S₁.R b (List.replicate (S₁.R a).length tick ++ S₁.R b) }) := by
  obtain ⟨v₂, hu, he₂⟩ := ucopy_exec body hab hat hbt v₁ S₁ ht
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_umul (he : Exec body p s m (mk v₁ S₁)) (c : ℕ) {a b t : Fin T} (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ht : S₁.R t = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (umul c a b t)) s (m + (4 * (S₁.R a).length + 4))
        (mk v₂ { S₁ with
          R := Function.update S₁.R b (List.replicate (c * (S₁.R a).length) tick ++ S₁.R b) }) := by
  obtain ⟨v₂, hu, he₂⟩ := umul_exec body c hab hat hbt v₁ S₁ ht
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_usub (he : Exec body p s m (mk v₁ S₁)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ht : S₁.R t = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (usub a b t)) s (m + (4 * (S₁.R a).length + 4))
        (mk v₂ { S₁ with R := Function.update S₁.R b ((S₁.R b).drop (S₁.R a).length) }) := by
  obtain ⟨v₂, hu, he₂⟩ := usub_exec body hab hat hbt v₁ S₁ ht
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_uclear (he : Exec body p s m (mk v₁ S₁)) (a : Fin T) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (uclear a)) s (m + (2 * (S₁.R a).length + 2))
        (mk v₂ { S₁ with R := Function.update S₁.R a [] }) := by
  obtain ⟨v₂, hu, he₂⟩ := uclear_exec body a v₁ S₁
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_zeroBits (he : Exec body p s m (mk v₁ S₁)) {len z t : Fin T} (hlz : len ≠ z)
    (hlt : len ≠ t) (hzt : z ≠ t) (ht : S₁.R t = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (zeroBits len z t)) s (m + (4 * (S₁.R len).length + 4))
        (mk v₂ { S₁ with
          R := Function.update S₁.R z (binSyms (S₁.R len).length 0 ++ S₁.R z) }) := by
  obtain ⟨v₂, hu, he₂⟩ := zeroBits_exec body hlz hlt hzt v₁ S₁ ht
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_binConv (he : Exec body p s m (mk v₁ S₁)) {a d t₁ t₂ : Fin T}
    (hreg : [a, d, t₁, t₂].Nodup) (hd : S₁.R d = []) (ht₁ : S₁.R t₁ = []) (ht₂ : S₁.R t₂ = []) :
    ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧ m₂ ≤ m + (16 * (S₁.R a).length + 4) ∧
      Exec body (.seq p (sxBinConv a d t₁ t₂)) s m₂
        (mk v₂ { S₁ with R := Function.update S₁.R d ((sxBits (S₁.R a).length).map bitSymbol) }) := by
  obtain ⟨v₂, m₂, hu, hm, he₂⟩ := sxBinConv_exec body hreg v₁ S₁ hd ht₁ ht₂
  exact ⟨v₂, _, hu, by omega, Exec.seq he he₂⟩

lemma sx_then_upow2 (he : Exec body p s m (mk v₁ S₁)) {a b t₁ t₂ : Fin T}
    (hreg : [a, b, t₁, t₂].Nodup) (ht₁ : S₁.R t₁ = []) (ht₂ : S₁.R t₂ = []) :
    ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧
      m₂ ≤ m + (4 * (2 ^ (S₁.R a).length * (S₁.R b).length) + 9 * (S₁.R a).length + 4) ∧
      Exec body (.seq p (upow2 a b t₁ t₂)) s m₂
        (mk v₂ { S₁ with
          R := Function.update S₁.R b ((S₁.R b).flatMap (List.replicate (2 ^ (S₁.R a).length))) }) := by
  obtain ⟨v₂, m₂, hu, hm, he₂⟩ := upow2_exec body hreg v₁ S₁ ht₁ ht₂
  exact ⟨v₂, _, hu, by omega, Exec.seq he he₂⟩

lemma sx_then_bitMask (he : Exec body p s m (mk v₁ S₁)) {nR tR z cnt w t₁ : Fin T}
    (hreg : [nR, tR, z, cnt, w, t₁].Nodup) (hc : S₁.R cnt = []) (hw : S₁.R w = [])
    (ht₁ : S₁.R t₁ = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (bitMask nR tR z cnt w t₁)) s
        (m + (10 * (S₁.R nR).length + 4 * (S₁.R tR).length + 15))
        (mk v₂ { S₁ with
          R := Function.update S₁.R z (binSyms (S₁.R nR).length (2 ^ (S₁.R tR).length) ++ S₁.R z) }) := by
  obtain ⟨v₂, hu, he₂⟩ := bitMask_exec body hreg v₁ S₁ rfl rfl hc hw ht₁
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_then_sxMask (he : Exec body p s m (mk v₁ S₁)) {nR oR KR kR z cnt w t₁ t₂ : Fin T}
    (hreg : [nR, oR, KR, kR, z, cnt, w, t₁, t₂].Nodup) (b₀ b₁ : Bool) {X : ℕ}
    (hK : 1 ≤ (S₁.R KR).length) (hc : S₁.R cnt = []) (hw : S₁.R w = []) (ht₁ : S₁.R t₁ = [])
    (ht₂ : S₁.R t₂ = [])
    (hX₁ : ∀ q < (S₁.R oR).length, q < (S₁.R nR).length → X.testBit q = false)
    (hX₂ : ∀ i < (S₁.R kR).length, (S₁.R oR).length + (S₁.R KR).length * i < (S₁.R nR).length →
      X.testBit ((S₁.R oR).length + (S₁.R KR).length * i) = b₀)
    (hX₃ : ∀ i < (S₁.R kR).length, ∀ s, 0 < s → s < (S₁.R KR).length →
      (S₁.R oR).length + (S₁.R KR).length * i + s < (S₁.R nR).length →
      X.testBit ((S₁.R oR).length + (S₁.R KR).length * i + s) = b₁)
    (hX₄ : ∀ q, (S₁.R oR).length + (S₁.R KR).length * (S₁.R kR).length ≤ q →
      q < (S₁.R nR).length → X.testBit q = false) :
    ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧
      m₂ ≤ m + (10 * (S₁.R nR).length + 4 * (S₁.R oR).length +
        (S₁.R kR).length * (4 * (S₁.R KR).length + 9) + 18) ∧
      Exec body (.seq p (sxMask nR oR KR kR z cnt w t₁ t₂ b₀ b₁)) s m₂
        (mk v₂ { S₁ with R := Function.update S₁.R z (binSyms (S₁.R nR).length X ++ S₁.R z) }) := by
  obtain ⟨v₂, m₂, hu, hm, he₂⟩ := sxMask_exec body hreg b₀ b₁ v₁ S₁ rfl rfl rfl rfl hK hc hw ht₁
    ht₂ hX₁ hX₂ hX₃ hX₄
  exact ⟨v₂, _, hu, by omega, Exec.seq he he₂⟩

/-- Copy register `a` onto `b` in the same order: pop `a` onto `t` and `t₂`, move `t₂` onto `b`
(`t` is moved back onto `a`). -/
def sxDupR (a b t t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR a t (pushN t₂ (fun v => v.sym.getD blank) 1)) (moveR t₂ b id)

theorem sxDupR_exec {a b t t₂ : Fin T} (hreg : [a, b, t, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht : S.R t = []) (ht₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (sxDupR a b t t₂) (mk v S) (6 * (S.R a).length + 6)
        (mk v' { S with R := Function.update S.R b (S.R a ++ S.R b) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, hat, hat₂⟩, ⟨hbt, hbt₂⟩, htt₂⟩ := hreg
  obtain ⟨v₁, hu₁, he₁⟩ := scanR_exec' body hat
    (regFx_pushN t₂ 1 (fun v => v.sym.getD blank) id (fun v x hx => by simp [hx]))
    (frame_pushFx hat₂ 1 id) (frame_pushFx htt₂ 1 id) v S ht
  rw [foldl_pushFx] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t₂ b hbt₂.symm id v₁
    { S with
      R := Function.update S.R t₂
        (((S.R a).reverse.flatMap fun x => List.replicate 1 (id x)) ++ S.R t₂) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [ht₂]; ring
  · congr 2
    funext k
    simp only [movedR, Function.update_apply, ht₂, List.append_nil, List.map_id, id]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all

lemma sx_then_dupR (he : Exec body p s m (mk v₁ S₁)) {a b t t₂ : Fin T}
    (hreg : [a, b, t, t₂].Nodup) (ht : S₁.R t = []) (ht₂ : S₁.R t₂ = []) :
    ∃ v₂ : HS T Q A U, v₂.user = v₁.user ∧
      Exec body (.seq p (sxDupR a b t t₂)) s (m + (6 * (S₁.R a).length + 6))
        (mk v₂ { S₁ with R := Function.update S₁.R b (S₁.R a ++ S₁.R b) }) := by
  obtain ⟨v₂, hu, he₂⟩ := sxDupR_exec body hreg v₁ S₁ ht ht₂
  exact ⟨v₂, hu, Exec.seq he he₂⟩

lemma sx_push_exec (v : HS T Q A U) (S : Stacks T A) (h : Fin T) (y : Fin (A + 4)) :
    Exec body (.act (.push (.rt h) (fun _ => y) .done)) (mk v S) 1
      (mk v { S with R := Function.update S.R h (y :: S.R h) }) := by
  refine Exec.cast (Exec.act (body := body) _ _) rfl ?_
  simp [Action.run, update_rt]

lemma sx_then_push (he : Exec body p s m (mk v₁ S₁)) (h : Fin T) (y : Fin (A + 4)) :
    Exec body (.seq p (.act (.push (.rt h) (fun _ => y) .done))) s (m + 1)
      (mk v₁ { S₁ with R := Function.update S₁.R h (y :: S₁.R h) }) := by
  refine Exec.seq he (Exec.cast (Exec.act (body := body) _ _) rfl ?_)
  simp [Action.run, update_rt]

end Then


/-! ### The setup stages -/

section Stages

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable (ι : SXReg → Fin T) (par : SXPar → Fin T)

/-- Distinct registers: `ι` and `par` are injective with disjoint ranges. -/
structure SxEnv : Prop where
  hι : Function.Injective ι
  hpar : Function.Injective par
  hpι : ∀ x p, ι x ≠ par p

/-- The mask builder for the item pattern `(b₀, b₁)` on `z`: `K - ρ` zero bits on `z`, then the
pattern on the `ρ + L - K` bits below. -/
noncomputable def sxMaskProg (b₀ b₁ : Bool) (z : Fin T) : Pr P T Q A U :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (ucopy (par .K) (ι (.sc 2)) (ι (.sc 0)))
    (usub (par .ρ) (ι (.sc 2)) (ι (.sc 0))))
    (zeroBits (ι (.sc 2)) z (ι (.sc 0))))
    (ucopy (par .ρ) (ι (.sc 3)) (ι (.sc 0))))
    (ucopy (par .L) (ι (.sc 3)) (ι (.sc 0))))
    (usub (par .K) (ι (.sc 3)) (ι (.sc 0))))
    (sxMask (ι (.sc 3)) (par .ρ) (par .K) (par .L) z (ι (.sc 0)) (ι (.sc 1)) (ι (.sc 4))
      (ι (.sc 5)) b₀ b₁))
    (uclear (ι (.sc 2))))
    (uclear (ι (.sc 3)))

/-- The single-bit mask `2 ^ (ρ + L - K)` on `mtop`. -/
noncomputable def sxTopProg : Pr P T Q A U :=
  .seq (.seq (.seq (.seq
    (ucopy (par .ρ) (ι (.sc 3)) (ι (.sc 0)))
    (ucopy (par .L) (ι (.sc 3)) (ι (.sc 0))))
    (usub (par .K) (ι (.sc 3)) (ι (.sc 0))))
    (bitMask (par .L) (ι (.sc 3)) (ι .mtop) (ι (.sc 0)) (ι (.sc 1)) (ι (.sc 4))))
    (uclear (ι (.sc 3)))

/-- The interchange header register `k` of bank `c`. -/
noncomputable def sxHdrReg (c : Fin 3) (k : Fin 5) : Fin T := ι (.swp c (reg (Fin.castSucc k : Fin 6)))

/-- The start of header `k`: a copy of its high bits, or a single one. -/
noncomputable def sxHdrStart (c : Fin 3) : Fin 5 → Pr P T Q A U
  | 0 => sxDupR (ι .rbin) (sxHdrReg ι c 0) (ι (.sc 0)) (ι (.sc 1))
  | 1 => .act (.push (.rt (sxHdrReg ι c 1)) (fun _ => bitSymbol true) .done)
  | 2 => sxDupR (ι .bbin) (sxHdrReg ι c 2) (ι (.sc 0)) (ι (.sc 1))
  | k => sxDupR (ι .lbin) (sxHdrReg ι c k) (ι (.sc 0)) (ι (.sc 1))

/-- The registers holding the lengths of the low zero bits of header `k` of bank `c` (the empty
`sc 5` stands for nothing). -/
noncomputable def sxHdrZ : Fin 3 → Fin 5 → Fin 3 → Fin T
  | 0, 0 => ![ι .n0, ι (.sc 5), ι (.sc 5)]
  | 0, 1 => ![ι .n1, ι (.sc 5), ι (.sc 5)]
  | 0, 2 => ![ι .n3, par .L, ι .n2]
  | 1, 0 => ![ι .n1, par .L, ι .n0]
  | 1, 1 => ![ι .n2, ι (.sc 5), ι (.sc 5)]
  | 1, 2 => ![ι .n3, ι (.sc 5), ι (.sc 5)]
  | 2, 0 => ![ι .n0, ι (.sc 5), ι (.sc 5)]
  | 2, 1 => ![ι .n1, par .L, ι .n2]
  | 2, 2 => ![ι .n3, ι (.sc 5), ι (.sc 5)]
  | _, _ => ![ι (.sc 5), ι (.sc 5), ι (.sc 5)]

/-- Build header `k` of bank `c`: its high bits, its low zero bits, and the separator. -/
noncomputable def sxHdrProg (c : Fin 3) (k : Fin 5) : Pr P T Q A U :=
  .seq (.seq (.seq (.seq (sxHdrStart ι c k)
    (zeroBits (sxHdrZ ι par c k 0) (sxHdrReg ι c k) (ι (.sc 0))))
    (zeroBits (sxHdrZ ι par c k 1) (sxHdrReg ι c k) (ι (.sc 0))))
    (zeroBits (sxHdrZ ι par c k 2) (sxHdrReg ι c k) (ι (.sc 0))))
    (.act (.push (.rt (sxHdrReg ι c k)) (fun _ => separator) .done))

/-- The program of setup stage `s`. -/
noncomputable def sxStageProg (x y z : ℕ) : ℕ → Pr P T Q A U
  | 1 => .seq (ucopy (par .a₀) (ι .n3) (ι (.sc 0)))
      (umul (sxPos x y z 2) (par .L) (ι .n3) (ι (.sc 0)))
  | 2 => umul (sxPos x y z 1 - sxPos x y z 2 - 1) (par .L) (ι .n2) (ι (.sc 0))
  | 3 => umul (sxPos x y z 0 - sxPos x y z 1 - 1) (par .L) (ι .n1) (ι (.sc 0))
  | 4 => .seq (.seq (.seq (.seq (ucopy (par .n) (ι .n0) (ι (.sc 0)))
      (usub (par .a₀) (ι .n0) (ι (.sc 0))))
      (umul (sxPos x y z 0 + 1) (par .L) (ι (.sc 1)) (ι (.sc 0))))
      (usub (ι (.sc 1)) (ι .n0) (ι (.sc 0)))) (uclear (ι (.sc 1)))
  | 5 => sxBinConv (par .rows) (ι .rbin) (ι (.sc 0)) (ι (.sc 1))
  | 6 => ucopy (ι .rbin) (ι .rb) (ι (.sc 0))
  | 7 => zeroBits (ι .n3) (ι (.cf 0)) (ι (.sc 0))
  | 8 => zeroBits (par .L) (ι (.cf 1)) (ι (.sc 0))
  | 9 => zeroBits (ι .n2) (ι (.cf 2)) (ι (.sc 0))
  | 10 => zeroBits (par .L) (ι (.cf 3)) (ι (.sc 0))
  | 11 => zeroBits (ι .n1) (ι (.cf 4)) (ι (.sc 0))
  | 12 => zeroBits (par .L) (ι (.cf 5)) (ι (.sc 0))
  | 13 => zeroBits (ι .n0) (ι (.cf 6)) (ι (.sc 0))
  | 14 => zeroBits (ι .rb) (ι (.cf 7)) (ι (.sc 0))
  | 15 => ucopy (par .rw) (ι .ctrB) (ι (.sc 0))
  | 16 => .seq (ucopy (par .n) (ι .ctrK) (ι (.sc 0))) (ucopy (ι .rb) (ι .ctrK) (ι (.sc 0)))
  | 17 => .seq (ucopy (ι .ctrK) (ι .ctrKB) (ι (.sc 0))) (ucopy (par .rw) (ι .ctrKB) (ι (.sc 0)))
  | 18 => .seq (ucopy (par .rows) (ι .cnt) (ι (.sc 0)))
      (upow2 (par .n) (ι .cnt) (ι (.sc 0)) (ι (.sc 1)))
  | 19 => .seq (.seq (umul 3 (ι .ctrKB) (ι (.sc 2)) (ι (.sc 0)))
      (sxBinConv (ι (.sc 2)) (ι .bbin) (ι (.sc 0)) (ι (.sc 1)))) (uclear (ι (.sc 2)))
  | 20 => sxBinConv (par .L) (ι .lbin) (ι (.sc 0)) (ι (.sc 1))
  | 21 => sxMaskProg ι par true false (ι .msel)
  | 22 => sxMaskProg ι par false true (ι .mgrd)
  | 23 => sxTopProg ι par
  | s => if h : 24 ≤ s ∧ s ≤ 38 then
      sxHdrProg ι par ⟨(s - 24) / 5, by omega⟩ ⟨(s - 24) % 5, by omega⟩ else .act .done

/-- The step bound of setup stage `s`. -/
def sxStageCost (d : SxD) : ℕ → ℕ
  | 1 => 4 * d.a₀ + 4 * d.L + 8
  | 2 => 4 * d.L + 4
  | 3 => 4 * d.L + 4
  | 4 => 4 * d.n + 4 * d.a₀ + 4 * d.L + 6 * ((sxPos d.x d.y d.z 0 + 1) * d.L) + 18
  | 5 => 16 * d.R + 4
  | 6 => 4 * d.rb + 4
  | 7 => 4 * d.n3 + 4
  | 8 => 4 * d.L + 4
  | 9 => 4 * d.n2 + 4
  | 10 => 4 * d.L + 4
  | 11 => 4 * d.n1 + 4
  | 12 => 4 * d.L + 4
  | 13 => 4 * d.n0 + 4
  | 14 => 4 * d.rb + 4
  | 15 => 4 * d.rw + 4
  | 16 => 4 * d.n + 4 * d.rb + 8
  | 17 => 4 * d.kl + 4 * d.rw + 8
  | 18 => 4 * d.R + 4 * d.M + 9 * d.n + 8
  | 19 => 58 * d.Bk + 10
  | 20 => 16 * d.L + 4
  | 21 => 30 * (d.ρ + d.L + d.K) + d.L * (4 * d.K + 9) + 48
  | 22 => 30 * (d.ρ + d.L + d.K) + d.L * (4 * d.K + 9) + 48
  | 23 => 30 * (d.ρ + d.L + d.K) + 30
  | _ => 6 * (d.rb + 3 * d.Bk + d.L) + 4 * (d.n3 + d.n2 + d.n1 + d.n0 + 3 * d.L) + 19

/-- The specification of setup stage `s + 1`: from the file after `s` stages to the file after
`s + 1` stages. -/
def SxStageSpec (d : SxD) (R₀ : Fin T → List (Fin (A + 4))) (s : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = sxFill ι (sxBc A d) s R₀ →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ sxStageCost d (s + 1) ∧
      Exec body (sxStageProg ι par d.x d.y d.z (s + 1)) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc A d) (s + 1) R₀ })

variable {ι par}

lemma SxEnv.ne (h : SxEnv ι par) {a b : SXReg} (hab : a ≠ b) : ι a ≠ ι b := h.hι.ne hab

lemma SxEnv.hpι' (h : SxEnv ι par) (p : SXPar) (x : SXReg) : par p ≠ ι x := (h.hpι x p).symm

lemma SxEnv.fill_ι (h : SxEnv ι par) {bc : SXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = sxFill ι bc s R₀) (x : SXReg) :
    S.R (ι x) = if sxStage x ≤ s then bc x else [] := by
  rw [hS, sxFill_ι h.hι]

lemma SxEnv.fill_par (h : SxEnv ι par) {bc : SXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = sxFill ι bc s R₀)
    (p : SXPar) : S.R (par p) = R₀ (par p) := by
  rw [hS, sxFill_out _ _ _ (fun x => h.hpι x p)]

/-- A register file that differs from `F` only at `ι x`. -/
lemma sx_finish {F R' : Fin T → List (Fin (A + 4))} {x : SXReg} {c : List (Fin (A + 4))}
    (h₁ : R' (ι x) = c) (h₂ : ∀ t, t ≠ ι x → R' t = F t) : R' = Function.update F (ι x) c := by
  funext t
  by_cases ht : t = ι x
  · subst ht; rw [h₁, Function.update_self]
  · rw [Function.update_of_ne ht, h₂ t ht]

/-- The register file after a stage: the file after the previous stage with the stage register
set to its contents. -/
lemma sx_finish2 (henv : SxEnv ι par) {bc : SXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = sxFill ι bc s R₀)
    {x : SXReg} (hx : sxStage x = s + 1) {R' : Fin T → List (Fin (A + 4))}
    (h₁ : R' (ι x) = bc x) (h₂ : ∀ t, t ≠ ι x → R' t = S.R t) :
    R' = sxFill ι bc (s + 1) R₀ := by
  rw [← sxFill_step henv.hι _ R₀ hx, ← hS]
  exact sx_finish h₁ h₂

set_option hygiene false in
/-- Distinctness of named registers. -/
macro "sxne" : tactic => `(tactic| first
  | exact henv.ne (by decide)
  | exact henv.hpι _ _
  | exact henv.hpι' _ _
  | exact henv.hpar.ne (by decide))

set_option hygiene false in
/-- Evaluate a register file given by updates of named registers over a setup file. -/
macro "sxsimp" : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hR₀,
    sxStage, sxBc, SxD.par, reg_val, Fin.val_castSucc])

set_option hygiene false in
/-- `sxsimp` at a hypothesis and the goal. -/
macro "sxsimp" "at" h:ident : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hR₀,
    sxStage, sxBc, SxD.par, reg_val, Fin.val_castSucc] at $h:ident ⊢)

variable {d : SxD} {R₀ : Fin T → List (Fin (A + 4))}

lemma sxStage_1 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 0 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .a₀) (b := ι .n3) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_umul body he₁ (sxPos d.x d.y d.z 2) (a := par .L) (b := ι .n3)
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast he₂ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; omega
  · congr 2
    refine sx_finish2 henv hS (x := .n3) rfl ?_ ?_
    · sxsimp; simp [SxD.n3, sxN3]; ring
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_2 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 1 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body (sxPos d.x d.y d.z 1 - sxPos d.x d.y d.z 2 - 1)
    (a := par .L) (b := ι .n2) (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .n2) rfl ?_ ?_
    · sxsimp; simp [SxD.n2, sxN2]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_4 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 3 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .n) (b := ι .n0) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .a₀) (b := ι .n0) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_umul body he₂ (sxPos d.x d.y d.z 0 + 1) (a := par .L)
    (b := ι (.sc 1)) (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_usub body he₃ (a := ι (.sc 1)) (b := ι .n0) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_uclear body he₄ (ι (.sc 1))
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; ring_nf; omega
  · congr 2
    refine sx_finish2 henv hS (x := .n0) rfl ?_ ?_
    · sxsimp; simp [SxD.n0, sxN0]; omega
    · intro t ht
      by_cases h1 : t = ι (.sc 1)
      · subst h1; sxsimp
      · simp [Function.update_of_ne h1, Function.update_of_ne ht]

lemma sxStage_3 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 2 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body (sxPos d.x d.y d.z 0 - sxPos d.x d.y d.z 1 - 1)
    (a := par .L) (b := ι .n1) (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .n1) rfl ?_ ?_
    · sxsimp; simp [SxD.n1, sxN1]
    · intro t ht; sxsimp; simp [ht]

set_option hygiene false in
/-- Duplicate-free lists of named registers. -/
macro "sxnodup" : tactic => `(tactic|
  simp [List.nodup_cons, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι'])

lemma sxStage_5 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 4 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxBinConv_exec body (a := par .rows) (d := ι .rbin)
    (t₁ := ι (.sc 0)) (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp) (by sxsimp)
  refine ⟨v₁, m₁, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₁; omega
  · congr 2
    refine sx_finish2 henv hS (x := .rbin) rfl ?_ ?_
    · sxsimp
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_6 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 5 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := ι .rbin) (b := ι .rb) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb]
  · congr 2
    refine sx_finish2 henv hS (x := .rb) rfl ?_ ?_
    · sxsimp; simp [SxD.rb]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_cf0 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 6 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := ι .n3) (z := ι (.cf 0))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 0) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_cf1 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 7 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := par .L) (z := ι (.cf 1))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 1) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_cf2 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 8 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := ι .n2) (z := ι (.cf 2))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 2) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_cf3 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 9 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := par .L) (z := ι (.cf 3))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 3) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_cf4 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 10 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := ι .n1) (z := ι (.cf 4))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 4) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_cf5 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 11 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := par .L) (z := ι (.cf 5))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 5) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_cf6 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 12 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := ι .n0) (z := ι (.cf 6))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 6) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_cf7 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 13 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body (len := ι .rb) (z := ι (.cf 7))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .cf 7) rfl ?_ ?_
    · sxsimp; simp [SxD.len, idxLen, SxD.n3, SxD.n2, SxD.n1, SxD.n0]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_15 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 14 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .rw) (b := ι .ctrB) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp
  · congr 2
    refine sx_finish2 henv hS (x := .ctrB) rfl ?_ ?_
    · sxsimp
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_16 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 15 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .n) (b := ι .ctrK) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_ucopy body he₁ (a := ι .rb) (b := ι .ctrK) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast he₂ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb]; omega
  · congr 2
    refine sx_finish2 henv hS (x := .ctrK) rfl ?_ ?_
    · sxsimp; simp [SxD.kl, SxD.rb]; omega
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_17 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 16 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := ι .ctrK) (b := ι .ctrKB) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_ucopy body he₁ (a := par .rw) (b := ι .ctrKB) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast he₂ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; omega
  · congr 2
    refine sx_finish2 henv hS (x := .ctrKB) rfl ?_ ?_
    · sxsimp; simp [SxD.Bk]
    · intro t ht; sxsimp; simp [ht]

lemma sxStage_18 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 17 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .rows) (b := ι .cnt) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := sx_then_upow2 body he₁ (a := par .n) (b := ι .cnt)
    (t₁ := ι (.sc 0)) (t₂ := ι (.sc 1)) (by sxnodup) (by sxsimp) (by sxsimp)
  refine ⟨v₂, m₂, by rw [hu₂, hu₁], ?_, Exec.cast he₂ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₂; simp only [SxD.M]; nlinarith
  · congr 2
    refine sx_finish2 henv hS (x := .cnt) rfl ?_ ?_
    · sxsimp; simp [SxD.M, flatMap_replicate_of_replicate]
    · intro t ht; sxsimp; simp [ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_19 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 18 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body 3 (a := ι .ctrKB) (b := ι (.sc 2)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := sx_then_binConv body he₁ (a := ι (.sc 2)) (d := ι .bbin)
    (t₁ := ι (.sc 0)) (t₂ := ι (.sc 1)) (by sxnodup) (by sxsimp) (by sxsimp) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_uclear body he₂ (ι (.sc 2))
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast he₃ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₂; omega
  · congr 2
    refine sx_finish2 henv hS (x := .bbin) rfl ?_ ?_
    · sxsimp
    · intro t ht
      by_cases h1 : t = ι (.sc 2)
      · subst h1; sxsimp
      · simp [Function.update_of_ne h1, Function.update_of_ne ht]

lemma sxStage_20 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 19 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxBinConv_exec body (a := par .L) (d := ι .lbin)
    (t₁ := ι (.sc 0)) (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp) (by sxsimp)
  refine ⟨v₁, m₁, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₁; omega
  · congr 2
    refine sx_finish2 henv hS (x := .lbin) rfl ?_ ?_
    · sxsimp
    · intro t ht; sxsimp; simp [ht]

/-- Validity of the slot-XOR data. -/
structure SxD.Valid (d : SxD) : Prop where
  hρ : d.ρ < d.K
  hLK : d.L = d.K * d.k
  hk : 1 ≤ d.k
  hR : 1 ≤ d.R
  hrw : 1 ≤ d.rw
  hxy : d.x ≠ d.y
  hxz : d.x ≠ d.z
  hyz : d.y ≠ d.z
  hfit : d.a₀ + (sxPos d.x d.y d.z 0 + 1) * d.L ≤ d.n

lemma sx_sel_bits {K ρ : ℕ} (hK : 0 < K) (k' : ℕ) :
    (∀ q < ρ, (selMask K ρ k').testBit q = false) ∧
    (∀ i, ρ + K * i < ρ + K * k' → (selMask K ρ k').testBit (ρ + K * i) = true) ∧
    (∀ i s, 0 < s → s < K → (selMask K ρ k').testBit (ρ + K * i + s) = false) ∧
    (∀ q, ρ + K * k' ≤ q → (selMask K ρ k').testBit q = false) := by
  refine ⟨fun q hq => ?_, fun i hi => ?_, fun i s hs hsK => ?_, fun q hq => ?_⟩
  · rw [← Bool.not_eq_true, testBit_selMask]
    rintro ⟨i, _, rfl⟩; omega
  · rw [testBit_selMask]
    exact ⟨i, Nat.lt_of_mul_lt_mul_left (a := K) (by omega), by ring⟩
  · rw [← Bool.not_eq_true, testBit_selMask]
    rintro ⟨i', _, h⟩
    exact ne_stride (o := ρ) (i' := i') hs hsK (by rw [h, Nat.mul_comm])
  · rw [← Bool.not_eq_true, testBit_selMask]
    rintro ⟨i, hi, rfl⟩
    have : K * (i + 1) ≤ K * k' := Nat.mul_le_mul_left K hi
    rw [Nat.mul_succ] at this
    nlinarith

lemma sx_grd_bits {K ρ : ℕ} (_hK : 0 < K) (k' L : ℕ) (hL : ρ + K * k' ≤ L) :
    (∀ q < ρ, (guardMask K ρ k' L).testBit q = false) ∧
    (∀ i, (guardMask K ρ k' L).testBit (ρ + K * i) = false) ∧
    (∀ i s, 0 < s → s < K → ρ + K * i + s < ρ + K * k' →
      (guardMask K ρ k' L).testBit (ρ + K * i + s) = true) ∧
    (∀ q, ρ + K * k' ≤ q → (guardMask K ρ k' L).testBit q = false) := by
  refine ⟨fun q hq => ?_, fun i => ?_, fun i s hs hsK hlt => ?_, fun q hq => ?_⟩
  · rw [testBit_guardMask]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; rintro ⟨i, _, h1, _⟩; omega
  · rw [testBit_guardMask]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; rintro ⟨i', _, h1, h2⟩
    have h3 : K * i' < K * i := by nlinarith
    have h4 : i' < i := Nat.lt_of_mul_lt_mul_left h3
    have h5 : K * (i' + 1) ≤ K * i := Nat.mul_le_mul_left K h4
    rw [Nat.mul_succ] at h5
    nlinarith
  · rw [testBit_guardMask]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hi : i < k' := Nat.lt_of_mul_lt_mul_left (a := K) (by omega)
    exact ⟨by omega, i, hi, by nlinarith, by nlinarith⟩
  · rw [testBit_guardMask]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; rintro ⟨i, hi, _, h2⟩
    have : K * (i + 1) ≤ K * k' := Nat.mul_le_mul_left K hi
    rw [Nat.mul_succ] at this
    nlinarith

lemma sxStage_21 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : SxStageSpec body ι par d R₀ 20 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have hK := hv.hρ
  have hKL : d.K ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_right _ hv.hk
  have hn' : d.L + d.ρ - d.K = d.ρ + d.K * (d.k - 1) := by
    rw [hv.hLK, Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right d.K hv.hk; omega
  have hpad : d.ρ + d.K * (d.k - 1) + (d.K - d.ρ) = d.L := by
    rw [← hn']; omega
  obtain ⟨Y₁, Y₂, Y₃, Y₄⟩ := sx_sel_bits (ρ := d.ρ) (by omega : 0 < d.K) (d.k - 1)
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .K) (b := ι (.sc 2)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .ρ) (b := ι (.sc 2)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 2)) (z := ι .msel)
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_ucopy body he₃ (a := par .ρ) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_ucopy body he₄ (a := par .L) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₆, hu₆, he₆⟩ := sx_then_usub body he₅ (a := par .K) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := sx_then_sxMask body he₆ (nR := ι (.sc 3)) (oR := par .ρ)
    (KR := par .K) (kR := par .L) (z := ι .msel) (cnt := ι (.sc 0)) (w := ι (.sc 1))
    (t₁ := ι (.sc 4)) (t₂ := ι (.sc 5)) (by sxnodup) true false (X := selMask d.K d.ρ (d.k - 1))
    (by sxsimp; omega) (by sxsimp) (by sxsimp) (by sxsimp) (by sxsimp)
    (by sxsimp; intro q hq _; exact Y₁ q hq)
    (by sxsimp; intro i _ hi; exact Y₂ i (by omega))
    (by sxsimp; intro i _ s hs hsK hi; exact Y₃ i s hs hsK)
    (by sxsimp; intro q hq _; exact Y₄ q (by nlinarith))
  obtain ⟨v₈, hu₈, he₈⟩ := sx_then_uclear body he₇ (ι (.sc 2))
  obtain ⟨v₉, hu₉, he₉⟩ := sx_then_uclear body he₈ (ι (.sc 3))
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (20 + 1) =
    sxMaskProg ι par true false (ι .msel) from rfl]
  unfold sxMaskProg
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₉ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₇; nlinarith
  · congr 2
    refine sx_finish2 henv hS (x := .msel) rfl ?_ ?_
    · sxsimp
      have h := sx_binSyms_append_zero (A := A) (a := d.ρ + d.K * (d.k - 1)) (b := d.K - d.ρ)
        (fun t _ => rfl) (fun t h1 _ => Y₄ t h1)
      rw [hpad] at h
      rw [← h, hn']
    · intro t ht
      by_cases h2 : t = ι (.sc 2)
      · subst h2; sxsimp
      by_cases h3 : t = ι (.sc 3)
      · subst h3; sxsimp
      simp [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne ht]

lemma sxStage_22 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : SxStageSpec body ι par d R₀ 21 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have hK := hv.hρ
  have hKL : d.K ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_right _ hv.hk
  have hn' : d.L + d.ρ - d.K = d.ρ + d.K * (d.k - 1) := by
    rw [hv.hLK, Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right d.K hv.hk; omega
  have hpad : d.ρ + d.K * (d.k - 1) + (d.K - d.ρ) = d.L := by
    rw [← hn']; omega
  obtain ⟨Y₁, Y₂, Y₃, Y₄⟩ := sx_grd_bits (ρ := d.ρ) (by omega : 0 < d.K) (d.k - 1) d.L (by omega)
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .K) (b := ι (.sc 2)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .ρ) (b := ι (.sc 2)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 2)) (z := ι .mgrd)
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_ucopy body he₃ (a := par .ρ) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_ucopy body he₄ (a := par .L) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₆, hu₆, he₆⟩ := sx_then_usub body he₅ (a := par .K) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := sx_then_sxMask body he₆ (nR := ι (.sc 3)) (oR := par .ρ)
    (KR := par .K) (kR := par .L) (z := ι .mgrd) (cnt := ι (.sc 0)) (w := ι (.sc 1))
    (t₁ := ι (.sc 4)) (t₂ := ι (.sc 5)) (by sxnodup) false true (X := guardMask d.K d.ρ (d.k - 1) d.L)
    (by sxsimp; omega) (by sxsimp) (by sxsimp) (by sxsimp) (by sxsimp)
    (by sxsimp; intro q hq _; exact Y₁ q hq)
    (by sxsimp; intro i _ hi; exact Y₂ i)
    (by sxsimp; intro i _ s hs hsK hi; exact Y₃ i s hs hsK (by omega))
    (by sxsimp; intro q hq _; exact Y₄ q (by nlinarith))
  obtain ⟨v₈, hu₈, he₈⟩ := sx_then_uclear body he₇ (ι (.sc 2))
  obtain ⟨v₉, hu₉, he₉⟩ := sx_then_uclear body he₈ (ι (.sc 3))
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (21 + 1) =
    sxMaskProg ι par false true (ι .mgrd) from rfl]
  unfold sxMaskProg
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₉ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp at hm₇; nlinarith
  · congr 2
    refine sx_finish2 henv hS (x := .mgrd) rfl ?_ ?_
    · sxsimp
      have h := sx_binSyms_append_zero (A := A) (a := d.ρ + d.K * (d.k - 1)) (b := d.K - d.ρ)
        (fun t _ => rfl) (fun t h1 _ => Y₄ t h1)
      rw [hpad] at h
      rw [← h, hn']
    · intro t ht
      by_cases h2 : t = ι (.sc 2)
      · subst h2; sxsimp
      by_cases h3 : t = ι (.sc 3)
      · subst h3; sxsimp
      simp [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne ht]

lemma sxStage_23 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : SxStageSpec body ι par d R₀ 22 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have hK := hv.hρ
  have hKL : d.K ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_right _ hv.hk
  have hn' : d.L + d.ρ - d.K = d.ρ + (d.k - 1) * d.K := by
    rw [hv.hLK, Nat.mul_comm (d.k - 1), Nat.mul_sub_one]
    have := Nat.le_mul_of_pos_right d.K hv.hk; omega
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .ρ) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) v S (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_ucopy body he₁ (a := par .L) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_usub body he₂ (a := par .K) (b := ι (.sc 3)) (t := ι (.sc 0))
    (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_bitMask body he₃ (nR := par .L) (tR := ι (.sc 3)) (z := ι .mtop)
    (cnt := ι (.sc 0)) (w := ι (.sc 1)) (t₁ := ι (.sc 4)) (by sxnodup) (by sxsimp) (by sxsimp)
    (by sxsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_uclear body he₄ (ι (.sc 3))
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (22 + 1) =
    sxTopProg ι par from rfl]
  unfold sxTopProg
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; omega
  · congr 2
    refine sx_finish2 henv hS (x := .mtop) rfl ?_ ?_
    · sxsimp; rw [hn']
    · intro t ht
      by_cases h3 : t = ι (.sc 3)
      · subst h3; sxsimp
      simp [Function.update_of_ne h3, Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h00 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 23 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .rbin) (b := ι (.swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n0) (z := ι (.swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (23 + 1) =
    sxHdrProg ι par 0 0 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 0 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n0]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h01 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 24 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have he₁ := sx_push_exec body v S (ι (.swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) (bitSymbol true)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (v₁ := v) (len := ι .n1) (z := ι (.swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (24 + 1) =
    sxHdrProg ι par 0 1 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 0 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n1]
    · intro t ht; simp only [Function.update_of_ne ht]

lemma sxStage_h02 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 25 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .bbin) (b := ι (.swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n3) (z := ι (.swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := par .L) (z := ι (.swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι .n2) (z := ι (.swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (25 + 1) =
    sxHdrProg ι par 0 2 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 0 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n3, SxD.n2];
        (simp only [← List.append_assoc, List.replicate_append_replicate]; congr 2; omega)
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h03 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 26 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (26 + 1) =
    sxHdrProg ι par 0 3 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 0 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h04 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 27 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (27 + 1) =
    sxHdrProg ι par 0 4 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 0 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

lemma sxStage_h10 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 28 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .rbin) (b := ι (.swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n1) (z := ι (.swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := par .L) (z := ι (.swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι .n0) (z := ι (.swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (28 + 1) =
    sxHdrProg ι par 1 0 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 1 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n1, SxD.n0];
        (simp only [← List.append_assoc, List.replicate_append_replicate]; congr 2; omega)
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h11 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 29 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have he₁ := sx_push_exec body v S (ι (.swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) (bitSymbol true)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (v₁ := v) (len := ι .n2) (z := ι (.swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (29 + 1) =
    sxHdrProg ι par 1 1 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 1 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n2]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h12 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 30 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .bbin) (b := ι (.swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n3) (z := ι (.swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (30 + 1) =
    sxHdrProg ι par 1 2 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 1 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n3]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h13 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 31 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (31 + 1) =
    sxHdrProg ι par 1 3 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 1 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h14 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 32 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (32 + 1) =
    sxHdrProg ι par 1 4 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 1 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h20 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 33 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .rbin) (b := ι (.swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n0) (z := ι (.swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (33 + 1) =
    sxHdrProg ι par 2 0 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 2 (reg (Fin.castSucc (0 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n0]
    · intro t ht; simp only [Function.update_of_ne ht]

lemma sxStage_h21 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 34 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  have he₁ := sx_push_exec body v S (ι (.swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) (bitSymbol true)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (v₁ := v) (len := ι .n1) (z := ι (.swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := par .L) (z := ι (.swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι .n2) (z := ι (.swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (34 + 1) =
    sxHdrProg ι par 2 1 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 2 (reg (Fin.castSucc (1 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n2, SxD.n1];
        (simp only [← List.append_assoc, List.replicate_append_replicate]; congr 2; omega)
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h22 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 35 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .bbin) (b := ι (.swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι .n3) (z := ι (.swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (35 + 1) =
    sxHdrProg ι par 2 2 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 2 (reg (Fin.castSucc (2 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right, SxD.n3]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h23 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 36 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (36 + 1) =
    sxHdrProg ι par 2 3 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 2 (reg (Fin.castSucc (3 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

-- `hR₀` is used by the unhygienic `sxsimp` macro, which the linter cannot see.
set_option linter.unusedVariables false in
lemma sxStage_h24 (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) :
    SxStageSpec body ι par d R₀ 37 := by
  intro v S hS
  have hF := henv.fill_ι hS
  have hP := henv.fill_par hS
  obtain ⟨v₁, hu₁, he₁⟩ := sxDupR_exec body (a := ι .lbin) (b := ι (.swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) (t := ι (.sc 0))
    (t₂ := ι (.sc 1)) (by sxnodup) v S (by sxsimp) (by sxsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_zeroBits body he₁ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₃, hu₃, he₃⟩ := sx_then_zeroBits body he₂ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_zeroBits body he₃ (len := ι (.sc 5)) (z := ι (.swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))))
    (t := ι (.sc 0)) (by sxne) (by sxne) (by sxne) (by sxsimp)
  have he₅ := sx_then_push body he₄ (ι (.swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6)))) separator
  rw [show sxStageProg (A := A) (P := P) (Q := Q) (U := U) ι par d.x d.y d.z (37 + 1) =
    sxHdrProg ι par 2 4 from rfl]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [sxStageCost]; sxsimp; simp [SxD.rb, SxD.n3, SxD.n2, SxD.n1, SxD.n0]; (have := length_sxBits_le (3 * d.Bk); have := length_sxBits_le d.L; omega)
  · congr 2
    refine sx_finish2 henv hS (x := .swp 2 (reg (Fin.castSucc (4 : Fin 5) : Fin 6))) rfl ?_ ?_
    · sxsimp; simp [sxHs, sxHe, sxHbits, binSyms_zero_right]
    · intro t ht; simp only [Function.update_of_ne ht]

lemma sxStage_all (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : ∀ s < 38, SxStageSpec body ι par d R₀ s := by
  intro s hs
  interval_cases s
  exacts [sxStage_1 body henv hR₀, sxStage_2 body henv hR₀, sxStage_3 body henv hR₀,
    sxStage_4 body henv hR₀, sxStage_5 body henv hR₀, sxStage_6 body henv hR₀,
    sxStage_cf0 body henv hR₀, sxStage_cf1 body henv hR₀, sxStage_cf2 body henv hR₀,
    sxStage_cf3 body henv hR₀, sxStage_cf4 body henv hR₀, sxStage_cf5 body henv hR₀,
    sxStage_cf6 body henv hR₀, sxStage_cf7 body henv hR₀, sxStage_15 body henv hR₀,
    sxStage_16 body henv hR₀, sxStage_17 body henv hR₀, sxStage_18 body henv hR₀,
    sxStage_19 body henv hR₀, sxStage_20 body henv hR₀, sxStage_21 body henv hR₀ hv,
    sxStage_22 body henv hR₀ hv, sxStage_23 body henv hR₀ hv, sxStage_h00 body henv hR₀, sxStage_h01 body henv hR₀, sxStage_h02 body henv hR₀, sxStage_h03 body henv hR₀, sxStage_h04 body henv hR₀, sxStage_h10 body henv hR₀, sxStage_h11 body henv hR₀, sxStage_h12 body henv hR₀, sxStage_h13 body henv hR₀, sxStage_h14 body henv hR₀, sxStage_h20 body henv hR₀, sxStage_h21 body henv hR₀, sxStage_h22 body henv hR₀, sxStage_h23 body henv hR₀, sxStage_h24 body henv hR₀]

lemma sxStage_ofStage (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 38) : sxStage (sxOfStage j) = j := by
  interval_cases j <;> rfl

variable (ι par) in
/-- The setup: the 38 stages in order. -/
noncomputable def sxSetup (x y z : ℕ) : Pr P T Q A U :=
  Prog.seqList ((List.range 38).map fun i => sxStageProg ι par x y z (i + 1))

variable (ι) in
/-- The cleanup: clear the built registers, the last built first. -/
def sxCleanup : Pr P T Q A U :=
  Prog.seqList ((List.range 38).map fun i => uclear (ι (sxOfStage (38 - i))))

theorem sxSetup_exec (henv : SxEnv ι par) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) (h0 : ∀ x, R₀ (ι x) = []) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = R₀) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ ∑ i ∈ Finset.range 38, sxStageCost d (i + 1) + 1 ∧
      Exec body (sxSetup ι par d.x d.y d.z) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc A d) 38 R₀ }) := by
  have hall := sxStage_all body henv hR₀ hv
  obtain ⟨v', m, hu, hm, he⟩ := sx_chain_exec body (fun i => sxFill ι (sxBc A d) i R₀)
    (fun i => sxStageProg ι par d.x d.y d.z (i + 1)) (fun i => sxStageCost d (i + 1)) 38 0
    (fun i hi v S hS => by simpa using hall i hi v S (by simpa using hS)) v S
    (by rw [hS, sxFill_zero henv.hι _ R₀ h0 (sxBc_zero A d)])
  refine ⟨v', m, hu, by simpa using hm, ?_⟩
  unfold sxSetup
  simpa using he

theorem sxCleanup_exec (henv : SxEnv ι par) {R₁ : Fin T → List (Fin (A + 4))}
    (h0 : ∀ x, R₁ (ι x) = []) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = sxFill ι (sxBc A d) 38 R₁) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ ∑ i ∈ Finset.range 38, (2 * (sxBc A d (sxOfStage (38 - i))).length + 2) + 1 ∧
      Exec body (sxCleanup (P := P) (Q := Q) (U := U) ι) (mk v S) m (mk v' { S with R := R₁ }) := by
  obtain ⟨v', m, hu, hm, he⟩ := sx_chain_exec body (fun i => sxFill ι (sxBc A d) (38 - i) R₁)
    (fun i => uclear (ι (sxOfStage (38 - i))))
    (fun i => 2 * (sxBc A d (sxOfStage (38 - i))).length + 2) 38 0
    (fun i hi v S hS => by
      simp only [Nat.zero_add] at hS ⊢
      have hx : sxStage (sxOfStage (38 - i)) = 37 - i + 1 := by
        rw [sxStage_ofStage _ (by omega) (by omega)]; omega
      obtain ⟨v', hu, he⟩ := uclear_exec body (ι (sxOfStage (38 - i))) v S
      refine ⟨v', _, hu, ?_, Exec.cast he rfl ?_⟩
      · rw [hS, sxFill_ι henv.hι, ite_eq_left (by omega)]
      · congr 2
        have h := sxFill_unstep henv.hι (sxBc A d) R₁ hx
        rw [hS, show 38 - (i + 1) = 37 - i by omega, ← h, show 37 - i + 1 = 38 - i by omega])
    v S (by simpa using hS)
  refine ⟨v', m, hu, by simpa using hm, Exec.cast he rfl ?_⟩
  congr 2
  simp only [Nat.zero_add, Nat.sub_self]
  exact sxFill_zero henv.hι _ R₁ h0 (sxBc_zero A d)

end Stages

/-! ### The packed program on the built registers -/

section Instrs

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The interchange layout: headers on caller tapes `0, …, 4`, the payload on tape `5`. -/
def sxHd : Fin 5 → Fin 6 := Fin.castSucc

/-- The payload tape of the interchange. -/
def sxPay : Fin 6 := Fin.last 5

lemma sxHd_inj : Function.Injective sxHd := Fin.castSucc_injective 5

variable {T : ℕ}

/-- Bank `c` of interchange registers. -/
def sxBank (ι : SXReg → Fin T) (c : Fin 3) (j : Fin (swapT 6)) : Fin T := ι (.swp c j)

lemma sxBank_inj {ι : SXReg → Fin T} (hι : Function.Injective ι) (c : Fin 3) :
    Function.Injective (sxBank ι c) := fun a b h => by
  have := hι h
  simpa [sxBank] using this

lemma sxT_le {ι : SXReg → Fin T} (hι : Function.Injective ι) : swapT 6 ≤ T := by
  have := Fintype.card_le_of_injective _ (sxBank_inj hι 0)
  simpa using this

/-- The registers of the rotation pass. -/
def sxRot (ι : SXReg → Fin T) (src : Fin T) : RotReg → Fin T
  | .src => src
  | .ctr => ι .ctrKB
  | .tmp => ι .rtmp
  | .cnt => ι .cnt
  | .ctmp => ι .rctmp
  | .out => ι .rout
  | .dst d => ι (.rdst d)
  | .aux d => ι (.raux d)
  | .fld g => ι (.cf g.castSucc)
  | .prm => ι .msel
  | .spare r => ι (.rsp r)

lemma sxRot_inj {ι : SXReg → Fin T} (hι : Function.Injective ι) {src : Fin T}
    (hsrc : ∀ x, ι x ≠ src) : Function.Injective (sxRot ι src) := by
  intro a b h
  cases a <;> cases b <;> simp only [sxRot] at h <;>
    first
    | rfl
    | exact absurd h (hsrc _)
    | exact absurd h.symm (hsrc _)
    | (have := hι h; simp_all)

variable {Q Ka : ℕ} {U : Type} {P : Type}

/-- One instruction of the packed program: an interchange on the bank of its slot pair, or a
rotation pass. -/
noncomputable def sxInstr {ι : SXReg → Fin T} (hι : Function.Injective ι)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (src st : Fin T) :
    Instr → Pr P T Q (prime + Ka) U
  | .swap a b => swapPass sxHd sxPay sxHd_inj hQ (sxBank ι (sxCls a b)) (sxBank_inj hι _)
      (sxT_le hι) src (ι .stmp)
  | .rot neg b => rotPass neg b (sxRot ι src) st

/-- A list of instructions. -/
noncomputable def sxInstrs {ι : SXReg → Fin T} (hι : Function.Injective ι)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (src st : Fin T) :
    List Instr → Pr P T Q (prime + Ka) U
  | [] => .act .done
  | i :: is => .seq (sxInstr hι hQ src st i) (sxInstrs hι hQ src st is)

end Instrs


/-! ### Interchange headers -/

section Headers

lemma sx_value_rep_false (e : ℕ) (bs : List Bool) :
    Counter.value (List.replicate e false ++ bs) = 2 ^ e * Counter.value bs := by
  induction e with
  | zero => simp
  | succ e ih => simp [List.replicate_succ, Counter.value, ih, pow_succ]; ring

lemma sx_canonical_rep_false (e : ℕ) {bs : List Bool} (h : bs ≠ [])
    (hc : GrowingCounterData.Canonical bs) :
    GrowingCounterData.Canonical (List.replicate e false ++ bs) := by
  right
  rcases hc with hc | hc
  · exact absurd hc h
  · rw [List.getLast?_append, hc]; rfl

variable {d : SxD}

lemma sxHs_value (_hv : d.Valid) (a b : Fin 3) (k : Fin 5) :
    Counter.value (sxHs d (sxCls a b) k) = BinaryInterchangeRun.values
      (swapDims d.N₀ d.N₁ d.N₂ d.N₃ d.L a b).1 (swapDims d.N₀ d.N₁ d.N₂ d.N₃ d.L a b).2.1
      ((swapDims d.N₀ d.N₁ d.N₂ d.N₃ d.L a b).2.2 * (3 * d.Bk)) d.L d.L k := by
  unfold sxCls swapDims
  split_ifs <;> fin_cases k <;>
    simp [sxHs, sxHe, sxHbits, sx_value_rep_false, value_sxBits, BinaryInterchangeRun.values,
      SxD.N₀, SxD.N₁, SxD.N₂, SxD.N₃, Counter.value, pow_add] <;> (ring_nf; try simp)

lemma sxHs_canonical (hv : d.Valid) (c : Fin 3) (k : Fin 5) :
    GrowingCounterData.Canonical (sxHs d c k) := by
  have hR : 0 < d.R := hv.hR
  have hB : 0 < 3 * d.Bk := by unfold SxD.Bk; have := hv.hrw; omega
  fin_cases k
  · exact sx_canonical_rep_false _ (sxBits_ne_nil hR) (canonical_sxBits _)
  · exact sx_canonical_rep_false _ (by simp [sxHbits]) (Or.inr rfl)
  · exact sx_canonical_rep_false _ (sxBits_ne_nil hB) (canonical_sxBits _)
  · fin_cases c <;> simpa [sxHs, sxHe, sxHbits] using canonical_sxBits d.L
  · fin_cases c <;> simpa [sxHs, sxHe, sxHbits] using canonical_sxBits d.L

/-- A bound on the header lengths. -/
def sxHL (d : SxD) : ℕ := d.n3 + d.n2 + d.n1 + d.n0 + 3 * d.L + d.rb + 3 * d.Bk + 1

lemma sxHs_length_le (c : Fin 3) (k : Fin 5) : (sxHs d c k).length ≤ sxHL d := by
  have h1 := length_sxBits_le (3 * d.Bk)
  have h2 := length_sxBits_le d.L
  fin_cases c <;> fin_cases k <;> simp [sxHs, sxHe, sxHbits, sxHL, SxD.rb] <;> omega

end Headers

/-! ### The rectangle of the data -/

section RectD

variable {d : SxD}

lemma SxD.sum_eq (hv : d.Valid) : d.n3 + d.L + d.n2 + d.L + d.n1 + d.L + d.n0 = d.n :=
  sx_sum hv.hxy hv.hxz hv.hyz hv.hfit

lemma SxD.rect_eq (hv : d.Valid) : rectSize d.N₀ d.N₁ d.N₂ d.N₃ d.L = d.M := by
  have hs := SxD.sum_eq hv
  have h : rectSize d.N₀ d.N₁ d.N₂ d.N₃ d.L =
      d.R * 2 ^ (d.n3 + d.L + d.n2 + d.L + d.n1 + d.L + d.n0) := by
    simp only [rectSize, SxD.N₀, SxD.N₁, SxD.N₂, SxD.N₃, pow_add]; ring
  rw [h, hs]; rfl

lemma SxD.keyLen_eq (hv : d.Valid) : keyLen d.n0 d.n1 d.n2 d.n3 d.L d.rb = d.kl := by
  have hs := SxD.sum_eq hv
  simp only [keyLen, SxD.kl]; omega

end RectD

lemma sx_sum_fin_ite (N C : ℕ) (hN : 5 ≤ N) :
    ∑ j : Fin N, (if j.val < 5 then C else 0) = 5 * C := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 5 then C else 0) N]
  induction N, hN using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]; ring
  | succ N hN ih => rw [Finset.sum_range_succ, ih, ite_eq_right (by omega), Nat.add_zero]

/-! ### The instructions on the built registers -/

section InstrExec

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q Ka : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q (prime + Ka) U)
variable {ι : SXReg → Fin T} {par : SXPar → Fin T} {d : SxD}

/-- The vendored part of the step bound of one interchange (`swapConst` from
`BinaryInterchangeRun.uniform_bound`): `3 C (T + 12 t + 5) V max(1, L)^τ` for `V` keyed symbols. -/
noncomputable def sxSwapReal (d : SxD) (T : ℕ) : ℝ :=
  3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (d.M * d.Bk : ℕ) *
    ((max 1 d.L : ℕ) : ℝ) ^ Parameters.tau

/-- The linear part of the step bound of one interchange. -/
noncomputable def sxSwapNat (d : SxD) (T : ℕ) : ℕ :=
  6 * (5 * (sxHL d + 1)) + 34 * (d.M * d.Bk) + 2 * T + 6 * swapT 6 + 23

/-- The step bound of one interchange. -/
noncomputable def sxSwapCost (d : SxD) (T : ℕ) : ℝ := sxSwapReal d T + sxSwapNat d T

/-- The step bound of one rotation pass. -/
def sxRotCost (d : SxD) : ℕ := d.M * (12 * d.Bk + 12 * d.n + 84) + 13

/-- The step bound of one instruction. -/
noncomputable def sxICost (d : SxD) (T : ℕ) (i : Instr) : ℝ :=
  if i.isRot then (sxRotCost d : ℝ) else sxSwapCost d T

lemma sxBank_sum (henv : SxEnv ι par) {R₁ : Fin T → List (Fin (prime + Ka + 4))}
    {S : Stacks T (prime + Ka)} (hS : S.R = sxFill ι (sxBc (prime + Ka) d) 38 R₁) (c : Fin 3) :
    ∑ j, (S.R (sxBank ι c j)).length ≤ 5 * (sxHL d + 1) := by
  calc ∑ j, (S.R (sxBank ι c j)).length
      ≤ ∑ j : Fin (swapT 6), (if j.val < 5 then sxHL d + 1 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        rw [sxBank, hS, sxFill_ι henv.hι, ite_eq_left (sxStage_le _)]
        simp only [sxBc]
        split_ifs with h
        · simp only [List.length_cons, List.length_map]
          have := sxHs_length_le (d := d) c ⟨j.val, h⟩
          omega
        · simp
    _ = 5 * (sxHL d + 1) := sx_sum_fin_ite _ _ (by have := sx_five_lt_swapT; omega)

variable {src st : Fin T}

/-- **One interchange** on the bank of its slot pair. -/
lemma sxSwap_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hv : d.Valid)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) {a b : Fin 3} (hab : a ≠ b)
    {X : List (List (Fin (prime + Ka + 4)))} (hX : X.length = d.M)
    (hXB : ∀ r ∈ X, r.length = d.Bk) (hX8 : ∀ r ∈ X, ∀ s ∈ r, s.val < 8)
    {R₁ : Fin T → List (Fin (prime + Ka + 4))} (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hS : S.R = sxFill ι (sxBc (prime + Ka) d) 38 R₁) (hR₁ : R₁ src = X.flatten) :
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧ (m : ℝ) ≤ sxSwapCost d T ∧
      Exec body (sxInstr henv.hι hQ src st (.swap a b)) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update R₁ src
          (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) [.swap a b]) X).flatten) }) := by
  have hrect := SxD.rect_eq hv
  have hF : ∀ x, S.R (ι x) = sxBc (prime + Ka) d x := fun x => by
    rw [hS, sxFill_ι henv.hι, ite_eq_left (sxStage_le x)]
  have hsrcR : S.R src = X.flatten := by rw [hS, sxFill_out _ _ _ hsrc, hR₁]
  have hB : 0 < d.Bk := by unfold SxD.Bk; have := hv.hrw; omega
  obtain ⟨v', m, hu, hm, he⟩ := swapPass_exec_le body sxHd sxPay sxHd_inj hQ
    (sxBank ι (sxCls a b)) (sxBank_inj henv.hι _) (sxT_le henv.hι) src (ι .stmp)
    (hsrc _).symm (fun j => hsrc _) (fun j => henv.ne (fun h => SXReg.noConfusion h))
    d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) d.Bk a b hab
    (by unfold SxD.N₀; have := hv.hR; positivity) (by unfold SxD.N₁; positivity)
    (by unfold SxD.N₂; positivity) (by unfold SxD.N₃; positivity) hB X (hX.trans hrect.symm)
    hXB hX8 (sxHs d (sxCls a b)) (sxHs_value hv a b) (sxHs_canonical hv _) v S hL hsrcR
    (by rw [hF]; rfl)
    (by rw [sxBank, hF]; simp [sxBc, reg_val, sxPay])
    (fun j hj => by rw [sxBank, hF]; simp [sxBc]; omega)
    (fun k => by
      rw [sxBank, hF]
      simp only [sxBc]
      split
      · congr 3
      · rename_i h; exact absurd (by simp [reg_val, sxHd]) h)
    (fun i hi hk => by
      exfalso
      by_cases h : i.val < 5
      · exact hk ⟨i.val, h⟩ (Fin.ext rfl)
      · exact hi (Fin.ext (by simp [sxPay]; omega)))
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · refine hm.trans ?_
    have hsum := sxBank_sum henv hS (sxCls a b)
    rw [hrect]
    unfold sxSwapCost sxSwapReal sxSwapNat
    gcongr
  · congr 2
    rw [hS, sxFill_update henv.hι _ _ _ hsrc]

/-- **One rotation pass.** -/
lemma sxRotI_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st)
    (hv : d.Valid) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (neg b : Bool)
    {X : List (List (Fin (prime + Ka + 4)))} (hX : X.length = d.M)
    (hXB : ∀ r ∈ X, r.length = d.Bk)
    {R₁ : Fin T → List (Fin (prime + Ka + 4))} (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka))
    (hS : S.R = sxFill ι (sxBc (prime + Ka) d) 38 R₁) (hR₁ : R₁ src = X.flatten) :
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧ m ≤ sxRotCost d ∧
      Exec body (sxInstr henv.hι hQ src st (.rot neg b)) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update R₁ src
          (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) [.rot neg b]) X).flatten) }) := by
  have hrect := SxD.rect_eq hv
  have hF : ∀ x, S.R (ι x) = sxBc (prime + Ka) d x := fun x => by
    rw [hS, sxFill_ι henv.hι, ite_eq_left (sxStage_le x)]
  have hsrcR : S.R src = X.flatten := by rw [hS, sxFill_out _ _ _ hsrc, hR₁]
  have hB : 1 ≤ d.Bk := by unfold SxD.Bk; have := hv.hrw; omega
  obtain ⟨v', m, hu, hm, he⟩ := rotPass_exec body neg b (ι := sxRot ι src)
    (sxRot_inj henv.hι hsrc)
    (fun x hx => by cases x <;> simp [RotReg.isIdx] at hx <;> exact hst _)
    (N₀ := d.N₀) (N₁ := d.N₁) (N₂ := d.N₂) (N₃ := d.N₃) (L := d.L) (K := d.K) (ρ := d.ρ)
    (f := d.k) (n₀ := d.n0) (n₁ := d.n1) (n₂ := d.n2) (n₃ := d.n3) (R := d.R)
    (by have := hv.hρ; omega) rfl rfl rfl rfl hB (hX.trans hrect.symm) hXB
    (c := S.R (ι .ctrKB)) (by rw [hF]; simp [sxBc]) (kk := S.R (ι .cnt))
    (by rw [hF, hrect]; simp [sxBc]) v S hsrcR rfl rfl
    (by rw [show sxRot ι src .tmp = ι .rtmp from rfl, hF]; rfl)
    (by rw [show sxRot ι src .ctmp = ι .rctmp from rfl, hF]; rfl)
    (by rw [show sxRot ι src .out = ι .rout from rfl, hF]; rfl)
    (fun dd => by rw [show sxRot ι src (.dst dd) = ι (.rdst dd) from rfl, hF]; rfl)
    (fun dd => by rw [show sxRot ι src (.aux dd) = ι (.raux dd) from rfl, hF]; rfl)
    (fun g => by
      rw [show sxRot ι src (.fld g) = ι (.cf g.castSucc) from rfl, hF]
      simp only [sxBc, SxD.len]
      fin_cases g <;> rfl)
    (by rw [show sxRot ι src .prm = ι .msel from rfl, hF]; rfl)
    (fun r => by rw [show sxRot ι src (.spare r) = ι (.rsp r) from rfl, hF]; rfl)
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · have hs := SxD.sum_eq hv
    rw [hrect] at hm
    refine hm.trans (le_of_eq ?_)
    unfold sxRotCost
    congr 3
    omega
  · congr 2
    rw [show sxRot ι src .src = src from rfl, hS, sxFill_update henv.hι _ _ _ hsrc]

lemma sx_rankPerm_nil (N₀ N₁ N₂ N₃ L K ρ n : ℕ) :
    rankPerm N₀ N₁ N₂ N₃ L K ρ n [] = Equiv.refl _ := by
  ext j
  simp [rankPerm, progPerm, liftA]

lemma sx_moveRecs_refl {α : Type*} {M : ℕ} (l : List (List α)) (hl : l.length = M) :
    moveRecs (Equiv.refl (Fin M)) l = l := by
  subst hl
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  simp [moveRecs, List.getD_eq_getElem?_getD]

/-- **The instruction list.** -/
theorem sxInstrs_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st)
    (hv : d.Valid) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) :
    ∀ (is : List Instr), (∀ a b, Instr.swap a b ∈ is → a ≠ b) →
    ∀ (X : List (List (Fin (prime + Ka + 4)))), X.length = d.M → (∀ r ∈ X, r.length = d.Bk) →
      (∀ r ∈ X, ∀ s ∈ r, s.val < 8) →
    ∀ (R₁ : Fin T → List (Fin (prime + Ka + 4))) (v : HS T Q (prime + Ka) U)
      (S : Stacks T (prime + Ka)), (∀ y, S.L y = []) →
      S.R = sxFill ι (sxBc (prime + Ka) d) 38 R₁ → R₁ src = X.flatten →
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (is.map (sxICost d T)).sum + 1 ∧
      Exec body (sxInstrs henv.hι hQ src st is) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update R₁ src
          (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) is) X).flatten) }) := by
  intro is
  induction is with
  | nil =>
      intro _ X hX _ _ R₁ v S _ hS hR₁
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      rw [run_done, sx_rankPerm_nil, sx_moveRecs_refl X (hX.trans (SxD.rect_eq hv).symm), ← hR₁,
        Function.update_eq_self, ← hS]
  | cons i is ih =>
      intro hsw X hX hXB hX8 R₁ v S hL hS hR₁
      have hrect := SxD.rect_eq hv
      set X' := moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) [i]) X with hX'
      have hX'l : X'.length = d.M := by rw [hX', length_moveRecs, hrect]
      have hmem : ∀ r ∈ X', r ∈ X := fun r hr =>
        mem_moveRecs _ (hX.trans hrect.symm) hr
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ : ∃ (v₁ : HS T Q (prime + Ka) U) (m₁ : ℕ),
          v₁.user = v.user ∧ (m₁ : ℝ) ≤ sxICost d T i ∧
          Exec body (sxInstr henv.hι hQ src st i) (mk v S) m₁
            (mk v₁ { S with
              R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update R₁ src X'.flatten) }) := by
        cases i with
        | swap a b =>
            obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxSwap_exec body henv hsrc hv hQ
              (hsw a b List.mem_cons_self) hX hXB hX8 v S hL hS hR₁
            exact ⟨v₁, m₁, hu₁, by simpa [sxICost, Instr.isRot] using hm₁, he₁⟩
        | rot neg b =>
            obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxRotI_exec body henv hsrc hst hv hQ neg b hX
              hXB v S hS hR₁
            exact ⟨v₁, m₁, hu₁, by simpa [sxICost, Instr.isRot] using hm₁, he₁⟩
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih (fun a b h => hsw a b (List.mem_cons_of_mem _ h))
        X' hX'l (fun r hr => hXB r (hmem r hr)) (fun r hr => hX8 r (hmem r hr))
        (Function.update R₁ src X'.flatten) v₁
        { S with R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update R₁ src X'.flatten) } hL
        rfl (by simp)
      have hR : Function.update (Function.update R₁ src X'.flatten) src
          (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) is) X').flatten =
          Function.update R₁ src
            (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) (i :: is)) X).flatten := by
        rw [Function.update_idem, hX', ← moveRecs_rankPerm_append _ _ _ _ _ _ _ _ [i] is X
          (hX.trans hrect.symm)]
        rfl
      rw [← hR]
      refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
      push_cast
      simp only [List.map_cons, List.sum_cons]
      linarith

end InstrExec

/-! ### The key, repair and fix passes on the built registers -/

section PassExec

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable {ι : SXReg → Fin T} {par : SXPar → Fin T} {d : SxD} {src st : Fin T}

lemma sx_nodup (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) {l : List SXReg} (hl : l.Nodup) :
    (src :: l.map ι).Nodup := by
  refine List.nodup_cons.2 ⟨?_, hl.map henv.hι⟩
  simp only [List.mem_map, not_exists, not_and]
  exact fun x _ => hsrc x

lemma SxD.R_le (d : SxD) : d.R ≤ 2 ^ d.rb := (lt_two_pow_length_sxBits d.R).le

lemma sx_fill38 (henv : SxEnv ι par) {R₁ : Fin T → List (Fin (A + 4))} {S : Stacks T A}
    (hS : S.R = sxFill ι (sxBc A d) 38 R₁) (x : SXReg) : S.R (ι x) = sxBc A d x := by
  rw [hS, sxFill_ι henv.hι, ite_eq_left (sxStage_le x)]

/-- **The key pass** on the built registers. -/
lemma sxKey_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st)
    (hv : d.Valid) {l : List (List (Fin (A + 4)))} (hl : l.length = d.M)
    (hlB : ∀ r ∈ l, r.length = d.rw) {R₁ : Fin T → List (Fin (A + 4))} (v : HS T Q A U)
    (S : Stacks T A) (hS : S.R = sxFill ι (sxBc A d) 38 R₁) (hR₁ : R₁ src = l.flatten) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 106 * (d.M * (d.rw + d.kl + 1)) + 4 * d.kl + 37 ∧
      Exec body (keyPass d.σ src (ι .kacc) (ι .ctrB) (ι .ktmp) (ι .msel) (ι (.kt 0)) (ι (.kt 1))
          (ι (.kt 2)) st (fun j => ι (.cf j))) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc A d) 38 (Function.update R₁ src
          (keyRecs d.kl (addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (idealT d.L d.K d.ρ d.k)) l).flatten) }) := by
  have hrect := SxD.rect_eq hv
  have hF := sx_fill38 henv hS
  have hkl := SxD.keyLen_eq hv
  obtain ⟨v', m, hu, hm, he⟩ := keyPass_exec body (N₀ := d.N₀) (N₁ := d.N₁) (N₂ := d.N₂)
    (N₃ := d.N₃) (L := d.L) (n₀ := d.n0) (n₁ := d.n1) (n₂ := d.n2) (n₃ := d.n3) (rb := d.rb)
    (R := d.R) rfl d.R_le rfl rfl rfl d.K d.ρ d.k d.σ
    (src := src) (acc := ι .kacc) (ctrB := ι .ctrB) (tmp := ι .ktmp) (t0 := ι (.kt 0))
    (t1 := ι (.kt 1)) (t2 := ι (.kt 2)) (cm := ι .msel) (st := st) (cf := fun j => ι (.cf j))
    (by
      have := sx_nodup henv hsrc (l := [.kacc, .ctrB, .ktmp, .kt 0, .kt 1, .kt 2, .msel] ++
        List.ofFn SXReg.cf) (by decide)
      simpa [List.map_ofFn] using this)
    (by simp [fun x => (hst x).symm])
    hv.hrw l (hl.trans hrect.symm) hlB v S (by rw [hS, sxFill_out _ _ _ hsrc, hR₁])
    (hF _) (by rw [hF]; simp [sxBc]) (hF _) (hF _) (hF _) (hF _) (by rw [hF]; rfl)
    (fun j => by rw [hF]; rfl)
  rw [hkl, hrect] at *
  refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
  congr 2
  rw [hS, sxFill_update henv.hι _ _ _ hsrc]

/-- The exceptional addresses of the repair (margin `1`). -/
noncomputable def sxBad (d : SxD) : ℕ :=
  Nat.card {a // Bad d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ d.k 1 a}

/-- **The repair pass** on the built registers. -/
lemma sxRepair_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st)
    (hv : d.Valid) (hA : 14 ≤ A) {l : List (List (Fin (A + 4)))} (hl : l.length = d.M)
    (hlB : ∀ r ∈ l, r.length = d.rw) {R₁ : Fin T → List (Fin (A + 4))} (v : HS T Q A U)
    (S : Stacks T A) (hS : S.R = sxFill ι (sxBc A d) 38 R₁)
    (hR₁ : R₁ src = (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) (prog d.σ))
      (keyRecs d.kl (addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (idealT d.L d.K d.ρ d.k)) l)).flatten) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 103 * (d.M * (d.rw + d.kl + 1)) + 13 * (sxBad d * d.kl * (d.rw + d.kl + 1)) +
        18 * d.kl + 82 ∧
      Exec body (repairPass d.σ src (ι .pgR) (ι .pbR) (ι .pg) (ι .pb) (ι .ctrKB) (ι .ctrB) (ι .ctrK)
          (ι .cnt) (ι .ptmp) (ι .msel) (ι .mgrd) st (fun j => ι (.cf j)) (fun r => ι (.pus r)))
        (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc A d) 38 (Function.update R₁ src
          (moveRecs (addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (idealT d.L d.K d.ρ d.k)) l).flatten) }) := by
  have hrect := SxD.rect_eq hv
  have hF := sx_fill38 henv hS
  have hkl := SxD.keyLen_eq hv
  obtain ⟨v', m, hu, hm, he⟩ := repairPass_exec body (N₀ := d.N₀) (N₁ := d.N₁) (N₂ := d.N₂)
    (N₃ := d.N₃) (L := d.L) (n₀ := d.n0) (n₁ := d.n1) (n₂ := d.n2) (n₃ := d.n3) (rb := d.rb)
    (R := d.R) rfl d.R_le rfl rfl rfl hA hv.hρ (by rw [hv.hLK, Nat.mul_comm]) hv.hk d.σ
    (src := src) (gR := ι .pgR) (bR := ι .pbR) (g := ι .pg) (b := ι .pb) (ctrKB := ι .ctrKB)
    (ctrB := ι .ctrB) (ctrK := ι .ctrK) (cnt := ι .cnt) (tmp := ι .ptmp) (mkR := ι .msel)
    (gmR := ι .mgrd) (st := st) (cf := fun j => ι (.cf j)) (us := fun r => ι (.pus r))
    (by
      have := sx_nodup henv hsrc (l := [.pgR, .pbR, .pg, .pb, .ctrKB, .ctrB, .ctrK, .cnt, .ptmp] ++
        [.msel, .mgrd] ++ List.ofFn SXReg.pus ++ List.ofFn SXReg.cf) (by decide)
      simpa [List.map_ofFn] using this)
    (by simp [fun x => (hst x).symm])
    hv.hrw l (hl.trans hrect.symm) hlB v S (by rw [hS, sxFill_out _ _ _ hsrc, hR₁, hkl])
    (hF _) (hF _) (hF _) (hF _)
    (by rw [hF, hkl]; simp [sxBc, SxD.Bk]; omega)
    (by rw [hF]; simp [sxBc])
    (by rw [hF, hkl]; simp [sxBc])
    (by rw [hF, hrect]; simp [sxBc])
    (hF _) (by rw [hF]; rfl) (by rw [hF]; rfl) (fun r => hF _) (fun j => by rw [hF]; rfl)
  rw [hkl, hrect] at hm
  refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
  congr 2
  rw [hS, sxFill_update henv.hι _ _ _ hsrc]

/-- **The fix pass** on the built registers. -/
lemma sxFix_exec (henv : SxEnv ι par) (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st)
    (hv : d.Valid) {l : List (List (Fin (A + 4)))} (hl : l.length = d.M)
    (hlB : ∀ r ∈ l, r.length = d.rw) {R₁ : Fin T → List (Fin (A + 4))} (v : HS T Q A U)
    (S : Stacks T A) (hS : S.R = sxFill ι (sxBc A d) 38 R₁) (hR₁ : R₁ src = l.flatten) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 92 * (d.M * (d.rw + d.kl + 1)) + 8 * d.kl + 82 ∧
      Exec body (fixPass d.σ src (ι (.fr 0)) (ι (.fr 1)) (ι (.fr 2)) (ι (.fr 3)) (ι (.fq 0))
          (ι (.fq 1)) (ι (.fq 2)) (ι (.fq 3)) (ι .ctrB) (ι .cnt) (ι .ftmp) (ι .mtop) st
          (fun j => ι (.cf j)) (fun r => ι (.fus r))) (mk v S) m
        (mk v' { S with R := sxFill ι (sxBc A d) 38 (Function.update R₁ src
          (moveRecs (addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (topFix d.L d.K d.ρ d.k)) l).flatten) }) := by
  have hrect := SxD.rect_eq hv
  have hF := sx_fill38 henv hS
  have hkl := SxD.keyLen_eq hv
  obtain ⟨v', m, hu, hm, he⟩ := fixPass_exec body (N₀ := d.N₀) (N₁ := d.N₁) (N₂ := d.N₂)
    (N₃ := d.N₃) (L := d.L) (n₀ := d.n0) (n₁ := d.n1) (n₂ := d.n2) (n₃ := d.n3) (rb := d.rb)
    (R := d.R) rfl d.R_le rfl rfl rfl hv.hρ (by rw [hv.hLK, Nat.mul_comm]) hv.hk d.σ
    (src := src) (r0 := ι (.fr 0)) (r1 := ι (.fr 1)) (r2 := ι (.fr 2)) (r3 := ι (.fr 3))
    (q0 := ι (.fq 0)) (q1 := ι (.fq 1)) (q2 := ι (.fq 2)) (q3 := ι (.fq 3)) (ctrB := ι .ctrB)
    (cnt := ι .cnt) (tmp := ι .ftmp) (tm := ι .mtop) (st := st) (cf := fun j => ι (.cf j))
    (us := fun r => ι (.fus r))
    (by
      have := sx_nodup henv hsrc (l := [.fr 0, .fr 1, .fr 2, .fr 3, .fq 0, .fq 1, .fq 2, .fq 3,
        .ctrB, .cnt, .ftmp] ++ [.mtop] ++ List.ofFn SXReg.fus ++ List.ofFn SXReg.cf) (by decide)
      simpa [List.map_ofFn] using this)
    (by simp [fun x => (hst x).symm])
    hv.hrw l (hl.trans hrect.symm) hlB v S (by rw [hS, sxFill_out _ _ _ hsrc, hR₁])
    (hF _) (hF _) (hF _) (hF _) (hF _) (hF _) (hF _) (hF _)
    (by rw [hF]; simp [sxBc])
    (by rw [hF, hrect]; simp [sxBc])
    (hF _) (by rw [hF]; rfl) (fun r => hF _) (fun j => by rw [hF]; rfl)
  rw [hkl, hrect] at hm
  refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
  congr 2
  rw [hS, sxFill_update henv.hι _ _ _ hsrc]

end PassExec

/-! ### The slot XOR -/

section Main

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Layer (m)

lemma sx_prog_swap_ne : ∀ σ : Equiv.Perm (Fin 3), ∀ a b : Fin 3, Instr.swap a b ∈ prog σ → a ≠ b := by
  decide

lemma sx_sum_map_ite (a b : ℝ) : ∀ l : List Instr,
    (l.map fun i => if i.isRot then a else b).sum =
      l.countP Instr.isRot * a + l.countP (fun i => !i.isRot) * b
  | [] => by simp
  | i :: l => by
      rw [List.map_cons, List.sum_cons, sx_sum_map_ite a b l, List.countP_cons, List.countP_cons]
      cases i <;> simp [Instr.isRot] <;> ring

lemma sx_addrPerm_trans {N₀ N₁ N₂ N₃ L : ℕ} (σ : Equiv.Perm (Fin 3)) (Pm Pm' : Equiv.Perm (Tri L)) :
    (addrPerm N₀ N₁ N₂ N₃ L σ Pm).trans (addrPerm N₀ N₁ N₂ N₃ L σ Pm') =
      addrPerm N₀ N₁ N₂ N₃ L σ (Pm.trans Pm') := by
  ext j
  simp only [addrPerm, liftA, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  rfl

lemma sx_pairSym_lt_eight {A : ℕ} (hA : 4 ≤ A) (re im : Bool) :
    (IntegerMultBounds.MathlibTM2.Layer.pairSym A re im).val < 8 := by
  rw [IntegerMultBounds.MathlibTM2.Layer.pairSym_val hA]
  cases re <;> cases im <;> simp

/-- The records of an array: `R 2^n` records of `r w` pair symbols. -/
lemma sx_recSyms_facts {A w R r n : ℕ} (hA : 4 ≤ A) (Z : ZArr (Fin R × Fin r) n) :
    ((recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w)).length = R * 2 ^ n ∧
    (∀ x ∈ (recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w), x.length = r * w) ∧
    (∀ x ∈ (recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms A w), ∀ s ∈ x, s.val < 8) := by
  refine ⟨by simp [IntegerMultBounds.MathlibTM2.Layer.length_recList], ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨rec, hrec, rfl⟩ := hx
    simp only [recList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
      List.mem_range] at hrec
    obtain ⟨u, a, _, rfl⟩ := hrec
    rw [IntegerMultBounds.MathlibTM2.Layer.recSyms, IntegerMultBounds.MathlibTM2.Layer.length_flatMap_const _ w
      (IntegerMultBounds.MathlibTM2.Layer.length_coeffSyms A w)]
    simp
  · intro x hx s hs
    simp only [List.mem_map] at hx
    obtain ⟨rec, _, rfl⟩ := hx
    simp only [IntegerMultBounds.MathlibTM2.Layer.recSyms, List.mem_flatMap, IntegerMultBounds.MathlibTM2.Layer.coeffSyms,
      List.mem_ofFn] at hs
    obtain ⟨z, _, t, rfl⟩ := hs
    exact sx_pairSym_lt_eight hA _ _

/-- **The slot-XOR program** for the static slots `x, y, z`: build the registers, attach the keys,
run the packed program, repair, fix the top position, clear the registers. -/
noncomputable def slotXorProg {T Q Ka : ℕ} {U P : Type} {ι : SXReg → Fin T}
    (hι : Function.Injective ι) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (par : SXPar → Fin T)
    (src st : Fin T) (x y z : ℕ) : Pr P T Q (prime + Ka) U :=
  .seq (.seq (.seq (.seq (.seq
    (sxSetup ι par x y z)
    (keyPass (sxSigma x y z) src (ι .kacc) (ι .ctrB) (ι .ktmp) (ι .msel) (ι (.kt 0)) (ι (.kt 1))
      (ι (.kt 2)) st (fun j => ι (.cf j))))
    (sxInstrs hι hQ src st (prog (sxSigma x y z))))
    (repairPass (sxSigma x y z) src (ι .pgR) (ι .pbR) (ι .pg) (ι .pb) (ι .ctrKB) (ι .ctrB)
      (ι .ctrK) (ι .cnt) (ι .ptmp) (ι .msel) (ι .mgrd) st (fun j => ι (.cf j))
      (fun r => ι (.pus r))))
    (fixPass (sxSigma x y z) src (ι (.fr 0)) (ι (.fr 1)) (ι (.fr 2)) (ι (.fr 3)) (ι (.fq 0))
      (ι (.fq 1)) (ι (.fq 2)) (ι (.fq 3)) (ι .ctrB) (ι .cnt) (ι .ftmp) (ι .mtop) st
      (fun j => ι (.cf j)) (fun r => ι (.fus r))))
    (sxCleanup ι)

/-- The natural-number part of the step bound of the slot XOR (`bad` exceptional addresses). -/
noncomputable def sxNatCost (d : SxD) (T bad : ℕ) : ℕ :=
  (∑ i ∈ Finset.range 38, sxStageCost d (i + 1) + 1) +
  (106 * (d.M * (d.rw + d.kl + 1)) + 4 * d.kl + 37) +
  (8 * sxRotCost d + 10 * sxSwapNat d T + 1) +
  (103 * (d.M * (d.rw + d.kl + 1)) + 13 * (bad * d.kl * (d.rw + d.kl + 1)) + 18 * d.kl + 82) +
  (92 * (d.M * (d.rw + d.kl + 1)) + 8 * d.kl + 82) +
  (∑ i ∈ Finset.range 38, (2 * (sxBc 0 d (sxOfStage (38 - i))).length + 2) + 1)

lemma sx_length_sxBc (A : ℕ) (d : SxD) (x : SXReg) :
    (sxBc A d x).length = (sxBc 0 d x).length := by
  cases x <;> simp [sxBc]
  all_goals first | rfl | (split_ifs <;> simp)

lemma sxSwapCost_nonneg (d : SxD) (T : ℕ) : 0 ≤ sxSwapCost d T := by
  unfold sxSwapCost sxSwapReal
  have := swapConst_pos
  positivity

lemma sxPos_lt_m {x y z : Fin m} (p : Fin 3) : sxPos x y z p < m := by
  unfold sxPos sxSlot
  generalize sxSigma (x : ℕ) y z p = q
  fin_cases q <;> simp

/-- **The slot XOR.** For distinct static slots `x, y, z` of the active region (active bit `i` at
`e i = a₀ + ρ + K i`, slot `j` the bits `a₀ + L j + ρ + K c`, `c < k`, `L = K k`), on the stream
register `src` holding `encZ A w Z`, the program leaves `encZ A w (pullM e (sxXorCol x y) Z)` on
`src`: column `c` of slot `y` gains column `c` of slot `x`. Every other register ends as it
started and `user` is kept. The bound has the vendored interchange term (ten interchanges of
`R 2^n` keyed records of `Bk = r w + n + rb` symbols) and the explicit natural-number part
`sxNatCost`, with `sxBad d` exceptional addresses in the repair. -/
theorem slotXor_exec {T Q Ka : ℕ} {U P : Type} (body : P → Pr P T Q (prime + Ka) U)
    {ι : SXReg → Fin T} {par : SXPar → Fin T} (henv : SxEnv ι par) {src st : Fin T}
    (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st) (hA : 14 ≤ prime + Ka)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w : ℕ} {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k) (hR : 1 ≤ R) (hrw : 1 ≤ r * w)
    (hfit : a₀ + m * L ≤ n) {e : Fin (m * k) → Fin n} (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i)
    (Z : ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka))
    (hL : ∀ y, S.L y = []) (hSsrc : S.R src = encZ (prime + Ka) w Z)
    (hpar : ∀ p, (S.R (par p)).length = SxD.par ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ p)
    (hrest : ∀ x, S.R (ι x) = []) :
    ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      (c : ℝ) ≤ 10 * sxSwapReal ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ T +
        (sxNatCost ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ T
          (sxBad ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩) : ℕ) ∧
      Exec body (slotXorProg henv.hι hQ par src st x y z) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ (prime + Ka) w (pullM e (sxXorCol x y) Z)) }) := by
  set d : SxD := ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ with hd
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  have hxz' : (x : ℕ) ≠ z := fun h => hxz (Fin.ext h)
  have hyz' : (y : ℕ) ≠ z := fun h => hyz (Fin.ext h)
  have hfit' : a₀ + (sxPos x y z 0 + 1) * L ≤ n :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L (sxPos_lt_m 0)) a₀) hfit
  have hv : d.Valid := ⟨hρ, hLK, hk, hR, hrw, hxy', hxz', hyz', hfit'⟩
  have hrect := SxD.rect_eq hv
  obtain ⟨hl, hlB, hl8⟩ := sx_recSyms_facts (by omega : 4 ≤ prime + Ka) (w := w) Z
  set l := (recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms (prime + Ka) w) with hldef
  have hlM : l.length = d.M := hl
  -- the setup
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxSetup_exec body henv hpar hv hrest v S rfl
  -- the key pass
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := sxKey_exec body henv hsrc hst hv hlM hlB v₁
    { S with R := sxFill ι (sxBc (prime + Ka) d) 38 S.R } rfl
    (by rw [hSsrc, sx_encZ_eq_flatten])
  set πT := addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (idealT d.L d.K d.ρ d.k) with hπT
  set K₁ := keyRecs d.kl πT l with hK₁
  have hK₁l : K₁.length = d.M := by rw [hK₁, length_keyRecs, hrect]
  have hK₁B : ∀ q ∈ K₁, q.length = d.Bk := fun q hq => by
    rw [keyRecs_length_mem _ _ _ _ (hlM.trans hrect.symm) hlB q hq, SxD.Bk]; ring
  have hK₁8 : ∀ q ∈ K₁, ∀ s ∈ q, s.val < 8 := by
    intro q hq s hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hq
    rcases List.mem_append.1 hs with hs | hs
    · simp only [binSyms, List.mem_ofFn] at hs
      obtain ⟨t, rfl⟩ := hs
      cases (Nat.testBit _ _) <;> simp [bitSymbol]
    · have hj : (j : ℕ) < l.length := by rw [hlM, ← hrect]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hj] at hs
      exact hl8 _ (List.getElem_mem hj) s hs
  -- the packed program
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := sxInstrs_exec body henv hsrc hst hv hQ (prog d.σ)
    (sx_prog_swap_ne _) K₁ hK₁l hK₁B hK₁8 (Function.update S.R src K₁.flatten) v₂
    { S with R := sxFill ι (sxBc (prime + Ka) d) 38 (Function.update S.R src K₁.flatten) } hL rfl
    (by simp)
  -- the repair
  set R₃ := Function.update (Function.update S.R src K₁.flatten) src
      (moveRecs (rankPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.K d.ρ (d.k - 1) (prog d.σ)) K₁).flatten
    with hR₃
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := sxRepair_exec body henv hsrc hst hv hA hlM hlB
    (R₁ := R₃) v₃ { S with R := sxFill ι (sxBc (prime + Ka) d) 38 R₃ } rfl
    (by rw [hR₃, Function.update_self])
  -- the top fixup
  set l' := moveRecs πT l with hl'
  have hl'M : l'.length = d.M := by rw [hl', length_moveRecs, hrect]
  have hl'B : ∀ q ∈ l', q.length = d.rw :=
    moveRecs_length_mem _ _ (hlM.trans hrect.symm) hlB
  set R₄ := Function.update R₃ src l'.flatten with hR₄
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := sxFix_exec body henv hsrc hst hv hl'M hl'B
    (R₁ := R₄) v₄ { S with R := sxFill ι (sxBc (prime + Ka) d) 38 R₄ } rfl
    (by rw [hR₄, Function.update_self])
  -- the cleanup
  set πF := addrPerm d.N₀ d.N₁ d.N₂ d.N₃ d.L d.σ (topFix d.L d.K d.ρ d.k) with hπF
  set R₅ := Function.update R₄ src (moveRecs πF l').flatten with hR₅
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := sxCleanup_exec body henv (R₁ := R₅)
    (fun x => by simp [hR₅, hR₄, hR₃, Function.update_of_ne (hsrc x), hrest]) v₅
    { S with R := sxFill ι (sxBc (prime + Ka) d) 38 R₅ } rfl
  -- the result
  have hres : (moveRecs πF l').flatten = encZ (prime + Ka) w (pullM e (sxXorCol x y) Z) := by
    rw [hl', ← moveRecs_trans _ _ _ (hlM.trans hrect.symm), hπT, hπF, sx_addrPerm_trans]
    have hx : (idealT d.L d.K d.ρ d.k).trans (topFix d.L d.K d.ρ d.k) = xorSel d.L d.K d.ρ d.k := by
      rw [xorSel_eq _ _ _ _ (by have := hv.hρ; omega) hk]; rfl
    rw [hx]
    exact sx_moveRecs_xorSel hxy hxz hyz hρ hLK hfit' he d.R_le rfl rfl rfl rfl Z
  have hfinal : R₅ = Function.update S.R src (encZ (prime + Ka) w (pullM e (sxXorCol x y) Z)) := by
    simp only [hR₅, hR₄, hR₃, Function.update_idem]
    rw [hres]
  rw [← hfinal]
  refine ⟨v₆, m₁ + m₂ + m₃ + m₄ + m₅ + m₆, hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans
    (hu₂.trans hu₁)))), ?_, Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq he₁ he₂)
      he₃) he₄) he₅) he₆⟩
  -- the step bound
  have hsum := sx_sum_map_ite (sxRotCost d : ℝ) (sxSwapCost d T) (prog d.σ)
  obtain ⟨hc8, hc10⟩ := prog_counts d.σ
  have hsw := sxSwapCost_nonneg d T
  have hm₃' : (m₃ : ℝ) ≤ 8 * (sxRotCost d : ℝ) + 10 * sxSwapCost d T + 1 := by
    refine hm₃.trans ?_
    have h1 : ((prog d.σ).map (sxICost d T)).sum =
        ((prog d.σ).map fun i => if i.isRot then (sxRotCost d : ℝ) else sxSwapCost d T).sum :=
      rfl
    rw [h1, hsum, hc8]
    have h2 : ((prog d.σ).countP (fun i => !i.isRot) : ℝ) ≤ 10 := by exact_mod_cast hc10
    have h3 := mul_le_mul_of_nonneg_right h2 hsw
    simp only [Nat.cast_ofNat]
    linarith
  have hclean : ∑ i ∈ Finset.range 38,
      (2 * (sxBc (prime + Ka) d (sxOfStage (38 - i))).length + 2) =
      ∑ i ∈ Finset.range 38, (2 * (sxBc 0 d (sxOfStage (38 - i))).length + 2) :=
    Finset.sum_congr rfl fun i _ => by rw [sx_length_sxBc]
  rw [hclean] at hm₆
  have hnat : m₁ + m₂ + m₄ + m₅ + m₆ + (8 * sxRotCost d + 10 * sxSwapNat d T + 1) ≤
      sxNatCost d T (sxBad d) := by
    unfold sxNatCost; omega
  have hcast : ((m₁ + m₂ + m₄ + m₅ + m₆ : ℕ) : ℝ) +
      (8 * (sxRotCost d : ℝ) + 10 * (sxSwapNat d T : ℝ) + 1) ≤ (sxNatCost d T (sxBad d) : ℝ) := by
    exact_mod_cast hnat
  have hsplit : sxSwapCost d T = sxSwapReal d T + (sxSwapNat d T : ℝ) := rfl
  rw [hsplit] at hm₃'
  simp only [Nat.cast_add] at hcast ⊢
  linarith
end Main



/-! ### The step bound in closed form -/

section CostBound

/-- A uniform bound on the setup stages. -/
lemma sxStageCost_le (d : SxD) (s : ℕ) :
    sxStageCost d s ≤ 4 * d.M + 60 * (d.n + d.R + d.rw + d.rb + d.Bk + d.kl + d.L + d.K + d.ρ +
      d.a₀ + d.n3 + d.n2 + d.n1 + d.n0) + 6 * ((sxPos d.x d.y d.z 0 + 1) * d.L) +
      d.L * (4 * d.K + 9) + 200 := by
  unfold sxStageCost
  split <;> omega

/-- A uniform bound on the register contents. -/
lemma sxBc_length_le (A : ℕ) (d : SxD) (x : SXReg) :
    (sxBc A d x).length ≤ d.M + d.n3 + d.n2 + d.n1 + d.n0 + d.rb + d.rw + d.kl + 4 * d.Bk +
      4 * d.L + sxHL d + 1 := by
  have h1 := length_sxBits_le (3 * d.Bk)
  have h2 := length_sxBits_le d.L
  cases x with
  | cf j => fin_cases j <;> simp [sxBc, SxD.len, idxLen] <;> omega
  | swp c j =>
      simp only [sxBc]
      split_ifs with h
      · have := sxHs_length_le (d := d) c ⟨j.val, h⟩
        simp; omega
      · simp
  | _ => simp [sxBc, SxD.rb] <;> omega

/-- **A closed form of the linear part of the slot-XOR bound**: with `M = R 2^n` records of
`r w` symbols and the key length `k' = n + rb`, at most
`20000 M (r w + k' + 1) + 13 |Bad| k' (r w + k' + 1) + 20 T + 60 t + 20000`. -/
lemma sxNatCost_le {d : SxD} (hv : d.Valid) (T bad : ℕ) :
    sxNatCost d T bad ≤ 20000 * (d.M * (d.rw + d.kl + 1)) +
      13 * (bad * d.kl * (d.rw + d.kl + 1)) + 20 * T + 60 * swapT 6 + 20000 := by
  set X := d.M * (d.rw + d.kl + 1) with hX
  have hR := hv.hR
  have hpow : 1 ≤ 2 ^ d.n := Nat.one_le_two_pow
  have hM2 : 2 ^ d.n ≤ d.M := by unfold SxD.M; exact Nat.le_mul_of_pos_left _ (by omega)
  have hRM : d.R ≤ d.M := by unfold SxD.M; exact Nat.le_mul_of_pos_right _ (by omega)
  have hM1 : 1 ≤ d.M := le_trans hpow hM2
  have hs := SxD.sum_eq hv
  have hKL : d.K ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_right _ hv.hk
  have hρK := hv.hρ
  have hfit := hv.hfit
  have hrbR : d.rb ≤ d.R := length_sxBits_le d.R
  have hkl : d.kl = d.n + d.rb := rfl
  have hBk : d.Bk = d.rw + d.kl := rfl
  have hY : d.rw + d.kl + 1 ≤ X := Nat.le_mul_of_pos_left _ (by omega)
  have hMX : d.M ≤ X := Nat.le_mul_of_pos_right _ (by omega)
  have hMBk : d.M * d.Bk ≤ X := Nat.mul_le_mul_left _ (by omega)
  have hrot : sxRotCost d ≤ 84 * X + 13 := by
    unfold sxRotCost
    have : d.M * (12 * d.Bk + 12 * d.n + 84) ≤ d.M * (84 * (d.rw + d.kl + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h84 : d.M * (84 * (d.rw + d.kl + 1)) = 84 * X := by rw [hX]; ring
    omega
  have hn2 : d.n ≤ 2 ^ d.n := (Nat.lt_two_pow_self).le
  have hLn : d.L ≤ d.n := by omega
  have hLLK : d.L * (4 * d.K + 9) ≤ 13 * X := by
    have h1 : d.L * (4 * d.K + 9) ≤ d.L * (13 * d.L) := Nat.mul_le_mul_left _ (by omega)
    have h2 : d.L * d.L ≤ d.n * d.n := Nat.mul_le_mul hLn hLn
    have h3 : d.n * d.n ≤ d.M * (d.rw + d.kl + 1) :=
      Nat.mul_le_mul (le_trans hn2 hM2) (by omega)
    nlinarith
  have hHL : sxHL d ≤ 5 * X := by unfold sxHL; omega
  have hhiL : (sxPos d.x d.y d.z 0 + 1) * d.L ≤ d.n := by omega
  have hsum1 : ∑ i ∈ Finset.range 38, sxStageCost d (i + 1) ≤
      38 * (4 * d.M + 60 * (d.n + d.R + d.rw + d.rb + d.Bk + d.kl + d.L + d.K + d.ρ +
        d.a₀ + d.n3 + d.n2 + d.n1 + d.n0) + 6 * ((sxPos d.x d.y d.z 0 + 1) * d.L) +
        d.L * (4 * d.K + 9) + 200) := by
    refine (Finset.sum_le_sum fun i _ => sxStageCost_le d (i + 1)).trans ?_
    simp
  have hsum2 : ∑ i ∈ Finset.range 38, (2 * (sxBc 0 d (sxOfStage (38 - i))).length + 2) ≤
      38 * (2 * (d.M + d.n3 + d.n2 + d.n1 + d.n0 + d.rb + d.rw + d.kl + 4 * d.Bk + 4 * d.L +
        sxHL d + 1) + 2) := by
    have hb : ∀ i ∈ Finset.range 38, 2 * (sxBc 0 d (sxOfStage (38 - i))).length + 2 ≤
        2 * (d.M + d.n3 + d.n2 + d.n1 + d.n0 + d.rb + d.rw + d.kl + 4 * d.Bk + 4 * d.L +
          sxHL d + 1) + 2 := fun i _ => by
      have := sxBc_length_le 0 d (sxOfStage (38 - i))
      omega
    refine (Finset.sum_le_sum hb).trans (by simp)
  unfold sxNatCost sxSwapNat
  omega

end CostBound

section CostMain

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Layer (m)

/-- **The slot XOR with a closed-form bound**: `slotXor_exec` with `sxNatCost_le`. With
`M = R 2^n` records, the key length `k' = n + rb` (`rb` the bit length of `R`), and `V = M (r w + k')`
keyed symbols, at most
`30 C (T + 12 t + 5) V max(1, L)^τ + 20000 M (r w + k' + 1) + 13 |Bad| k' (r w + k' + 1) + 20 T +
60 t + 20000` steps, `C = swapConst`, `t = swapT 6`, `|Bad| = sxBad d`. -/
theorem slotXor_exec_le {T Q Ka : ℕ} {U P : Type} (body : P → Pr P T Q (prime + Ka) U)
    {ι : SXReg → Fin T} {par : SXPar → Fin T} (henv : SxEnv ι par) {src st : Fin T}
    (hsrc : ∀ x, ι x ≠ src) (hst : ∀ x, ι x ≠ st) (hA : 14 ≤ prime + Ka)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w : ℕ} {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k) (hR : 1 ≤ R) (hrw : 1 ≤ r * w)
    (hfit : a₀ + m * L ≤ n) {e : Fin (m * k) → Fin n} (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i)
    (Z : IntegerMultBounds.MathlibTM2.Layer.ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hSsrc : S.R src = IntegerMultBounds.MathlibTM2.Layer.encZ (prime + Ka) w Z)
    (hpar : ∀ p, (S.R (par p)).length = SxD.par ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ p)
    (hrest : ∀ x, S.R (ι x) = []) :
    ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      (c : ℝ) ≤ 30 * swapConst * ((T + 12 * swapT 6 + 5 : ℕ) : ℝ) *
          ((R * 2 ^ n * (r * w + (n + (sxBits R).length)) : ℕ) : ℝ) *
          ((max 1 L : ℕ) : ℝ) ^ Parameters.tau +
        ((20000 * (R * 2 ^ n * (r * w + (n + (sxBits R).length) + 1)) +
          13 * (sxBad ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ * (n + (sxBits R).length) *
            (r * w + (n + (sxBits R).length) + 1)) + 20 * T + 60 * swapT 6 + 20000 : ℕ) : ℝ) ∧
      Exec body (slotXorProg henv.hι hQ par src st x y z) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src
            (IntegerMultBounds.MathlibTM2.Layer.encZ (prime + Ka) w (IntegerMultBounds.MathlibTM2.Layer.pullM e (sxXorCol x y) Z)) }) := by
  obtain ⟨v', c, hu, hc, hex⟩ := slotXor_exec body henv hsrc hst hA hQ hxy hxz hyz hρ hLK hk
    hR hrw hfit he Z v S hL hSsrc hpar hrest
  refine ⟨v', c, hu, hc.trans ?_, hex⟩
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  have hxz' : (x : ℕ) ≠ z := fun h => hxz (Fin.ext h)
  have hyz' : (y : ℕ) ≠ z := fun h => hyz (Fin.ext h)
  have hfit' : a₀ + (sxPos x y z 0 + 1) * L ≤ n :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L (sxPos_lt_m 0)) a₀) hfit
  have hv : SxD.Valid ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ :=
    ⟨hρ, hLK, hk, hR, hrw, hxy', hxz', hyz', hfit'⟩
  have hnat := sxNatCost_le hv T (sxBad ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩)
  have hnat' := (Nat.cast_le (α := ℝ)).2 hnat
  have hreal : 10 * sxSwapReal ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ T =
      30 * swapConst * ((T + 12 * swapT 6 + 5 : ℕ) : ℝ) *
        ((R * 2 ^ n * (r * w + (n + (sxBits R).length)) : ℕ) : ℝ) *
        ((max 1 L : ℕ) : ℝ) ^ Parameters.tau := by
    unfold sxSwapReal
    have hMB : ((SxD.M ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ *
        SxD.Bk ⟨a₀, K, ρ, L, R, n, r * w, k, x, y, z⟩ : ℕ) : ℝ) =
        ((R * 2 ^ n * (r * w + (n + (sxBits R).length)) : ℕ) : ℝ) := rfl
    rw [hMB]
    ring
  rw [hreal]
  exact add_le_add le_rfl hnat'

end CostMain


end IntegerMultBounds.MathlibTM2.Node
