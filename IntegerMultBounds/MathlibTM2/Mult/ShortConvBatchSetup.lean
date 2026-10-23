module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Shared batch counters and ring header from unary dimensions

Setup writes five owned words, independent of the number of records. Both block-symbol
counts are actual unary products; both padding counts and the header are generated programs.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- One operand's reusable block-symbol and padding counts. -/
def operandSetup (aR lR wR count pad t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct aR wR count t₁ t₂) (padding lR wR count pad t₁ t₂)

/-- Cost of generating one operand's two reusable counters. -/
def operandSetupCost (l w a : ℕ) : ℕ :=
  a * (4 * w + 9) + 4 + (4 * w + 4 * (2 ^ l * w) + 9 * l + 4 * (a * w) + 12)


theorem operandSetup_exec {aR lR wR count pad t₁ t₂ : Fin T}
    (hreg : [aR, lR, wR, count, pad, t₁, t₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (a l w : ℕ)
    (ha : (S.R aR).length = a) (hl : (S.R lR).length = l) (hw : (S.R wR).length = w)
    (hcount : S.R count = []) (hpad : S.R pad = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ operandSetupCost l w a ∧
      Exec body (operandSetup aR lR wR count pad t₁ t₂) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update S.R count (List.replicate (a * w) tick)) pad
          (List.replicate ((2 ^ l - a) * w) tick)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [aR, wR, count, t₁, t₂].Nodup by simp_all) v S ht₁ ht₂
  rw [ha, hw] at hn₁ he₁
  rw [hcount, List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate (a * w) tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := padding_exec (body := body)
    (show [lR, wR, count, pad, t₁, t₂].Nodup by simp_all) v₁ S₁
    (by simp [S₁, ‹count ≠ pad›.symm, hpad])
    (by simp [S₁, ‹count ≠ t₁›.symm, ht₁]) (by simp [S₁, ‹count ≠ t₂›.symm, ht₂])
  have hla : (S₁.R lR).length = l := by simpa [S₁, ‹lR ≠ count›] using hl
  have hwa : (S₁.R wR).length = w := by simpa [S₁, ‹wR ≠ count›] using hw
  have hca : (S₁.R count).length = a * w := by simp [S₁]
  rw [hla, hwa, hca] at hn₂ he₂
  rw [← Nat.sub_mul] at he₂
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by unfold operandSetupCost; omega, Exec.seq he₁ he₂⟩

/-- Roles used to prepare the shared batch parameters. -/
inductive SetupReg
  | p | l | w | a | b | countX | padX | countY | padY | header | ta | tb | acc | sv | tmp
  deriving DecidableEq

open SetupReg

/-- Exactly the five generated words, also the complete final cleanup list. -/
def setupWritten : List SetupReg := [.countX, .padX, .countY, .padY, .header]

/-- Work tapes used during parameter generation. -/
def setupScratch : List SetupReg := [.ta, .tb, .acc, .sv, .tmp]

/-- Contents of each generated word. Other roles are left unchanged by setup. -/
def setupValue (A p l w a b : ℕ) : SetupReg → List (Fin (A + 4))
  | .countX => List.replicate (a * w) tick
  | .padX => List.replicate ((2 ^ l - a) * w) tick
  | .countY => List.replicate (b * w) tick
  | .padY => List.replicate ((2 ^ l - b) * w) tick
  | .header => (header p (2 ^ l) w).map bitSymbol
  | _ => []

/-- The prepared bank changes only the five generated words. -/
def setupBank (j : SetupReg → Fin T) (R : Regs T A) (p l w a b : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update R (j .countX) (setupValue A p l w a b .countX))
      (j .padX) (setupValue A p l w a b .padX))
      (j .countY) (setupValue A p l w a b .countY))
      (j .padY) (setupValue A p l w a b .padY))
      (j .header) (setupValue A p l w a b .header)

theorem setupBank_at (j : SetupReg → Fin T) (hj : Function.Injective j)
    (R : Regs T A) (p l w a b : ℕ) (r : SetupReg) :
    setupBank j R p l w a b (j r) =
      if r ∈ setupWritten then setupValue A p l w a b r else R (j r) := by
  cases r <;> simp [setupBank, setupWritten, hj.eq_iff]

theorem setupBank_off (j : SetupReg → Fin T) (R : Regs T A) (p l w a b : ℕ) (k : Fin T)
    (hk : ∀ r ∈ setupWritten, k ≠ j r) : setupBank j R p l w a b k = R k := by
  simp [setupBank, hk .countX (by simp [setupWritten]), hk .padX (by simp [setupWritten]),
    hk .countY (by simp [setupWritten]), hk .padY (by simp [setupWritten]),
    hk .header (by simp [setupWritten])]

/-- Generate all reusable counters, then generate the header on the same fixed bank. -/
def batchSetup (j : SetupReg → Fin T) : Pr P T Q A U :=
  .seq (operandSetup (j .a) (j .l) (j .w) (j .countX) (j .padX) (j .ta) (j .tb))
    (.seq (operandSetup (j .b) (j .l) (j .w) (j .countY) (j .padY) (j .ta) (j .tb))
      (ldrHeader (j .p) (j .l) (j .w) (j .header) (j .ta) (j .tb) (j .acc) (j .sv) (j .tmp)))

def batchSetupCost (p l w a b : ℕ) : ℕ :=
  operandSetupCost l w a + operandSetupCost l w b + ldrHeaderCost p l w

/-- No prepared padding words or header are inputs to this program. All original dimension
symbols, other tapes and user state are preserved, and setup scratch is restored. -/
theorem batchSetup_exec (j : SetupReg → Fin T) (hj : Function.Injective j)
    (v : HS T Q A U) (S : Stacks T A) (p l w a b : ℕ)
    (hp : (S.R (j .p)).length = p) (hl : (S.R (j .l)).length = l)
    (hw : (S.R (j .w)).length = w) (ha : (S.R (j .a)).length = a) (hb : (S.R (j .b)).length = b)
    (hempty : ∀ r ∈ setupWritten ++ setupScratch, S.R (j r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchSetupCost p l w a b ∧
      Exec body (batchSetup j) (mk v S) n (mk v' { S with R := setupBank j S.R p l w a b }) := by
  have nd (rs : List SetupReg) (hnd : rs.Nodup) : (rs.map j).Nodup := hnd.map hj
  have empty (r : SetupReg) (hr : r ∈ setupWritten ++ setupScratch) := hempty r hr
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := operandSetup_exec (body := body)
    (by simpa using nd [.a, .l, .w, .countX, .padX, .ta, .tb] (by decide))
    v S a l w ha hl hw (empty _ (by simp [setupWritten])) (empty _ (by simp [setupWritten]))
    (empty _ (by simp [setupScratch])) (empty _ (by simp [setupScratch]))
  set S₁ : Stacks T A := { S with R := (Function.update
    (Function.update S.R (j .countX) (List.replicate (a * w) tick))
    (j .padX) (List.replicate ((2 ^ l - a) * w) tick)) }
  have e₁ (r : SetupReg) (h₁ : r ≠ .countX) (h₂ : r ≠ .padX) : S₁.R (j r) = S.R (j r) := by
    simp [S₁, hj.eq_iff, h₁, h₂]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := operandSetup_exec (body := body)
    (by simpa using nd [.b, .l, .w, .countY, .padY, .ta, .tb] (by decide))
    v₁ S₁ b l w (by rw [e₁ _ (by decide) (by decide)]; exact hb)
    (by rw [e₁ _ (by decide) (by decide)]; exact hl)
    (by rw [e₁ _ (by decide) (by decide)]; exact hw)
    (by rw [e₁ _ (by decide) (by decide)]; exact empty _ (by simp [setupWritten]))
    (by rw [e₁ _ (by decide) (by decide)]; exact empty _ (by simp [setupWritten]))
    (by rw [e₁ _ (by decide) (by decide)]; exact empty _ (by simp [setupScratch]))
    (by rw [e₁ _ (by decide) (by decide)]; exact empty _ (by simp [setupScratch]))
  set S₂ : Stacks T A := { S₁ with R := (Function.update
    (Function.update S₁.R (j .countY) (List.replicate (b * w) tick))
    (j .padY) (List.replicate ((2 ^ l - b) * w) tick)) }
  have e₂ (r : SetupReg) (hr : r ∈ [.p, .l, .w, .header, .ta, .tb, .acc, .sv, .tmp]) :
      S₂.R (j r) = S.R (j r) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S₂, S₁, hj.eq_iff]
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := ldrHeader_exec body
    (by simpa using nd [.p, .l, .w, .header, .ta, .tb, .acc, .sv, .tmp] (by decide)) v₂ S₂
    (by rw [e₂ .ta (by simp)]; exact empty _ (by simp [setupScratch]))
    (by rw [e₂ .tb (by simp)]; exact empty _ (by simp [setupScratch]))
    (by rw [e₂ .acc (by simp)]; exact empty _ (by simp [setupScratch]))
    (by rw [e₂ .sv (by simp)]; exact empty _ (by simp [setupScratch]))
    (by rw [e₂ .tmp (by simp)]; exact empty _ (by simp [setupScratch]))
  rw [e₂ .p (by simp), e₂ .l (by simp), e₂ .w (by simp), hp, hl, hw] at hn₃ he₃
  rw [e₂ .header (by simp), empty .header (by simp [setupWritten]), List.append_nil] at he₃
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  unfold batchSetupCost
  omega

/-- The generated counters contain two padded-record widths in total. -/
theorem setup_length_sum (p l w a b : ℕ) (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    (setupWritten.map fun r => (setupValue A p l w a b r).length).sum =
      2 * (2 ^ l * w) + (header p (2 ^ l) w).length := by
  have hA : a * w + (2 ^ l - a) * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  have hB : b * w + (2 ^ l - b) * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hb]
  simp [setupWritten, setupValue]
  omega

/-- Setup has linear cost in the padded record size and the input dimensions. -/
theorem batchSetupCost_le (p l w a b : ℕ) (hw : 1 ≤ w) (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    batchSetupCost p l w a b ≤ 42 * (2 ^ l * w) + 8 * w + 18 * l +
      ldrHeaderCost p l w + 32 := by
  have haW := Nat.mul_le_mul_right w ha
  have hbW := Nat.mul_le_mul_right w hb
  have ha₁ : a ≤ a * w := by simpa using Nat.mul_le_mul_left a hw
  have hb₁ : b ≤ b * w := by simpa using Nat.mul_le_mul_left b hw
  unfold batchSetupCost operandSetupCost
  ring_nf at haW hbW ha₁ hb₁ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
