module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRegisters
public import IntegerMultBounds.MathlibTM2.Layer.Reverse
public import IntegerMultBounds.MathlibTM2.Node.Factor

/-! **Translations without child calls.** Reversing a wire register in place (three moves through
the wire's temporary and the spare) replaces its array `Z` by `zrev Z`: every address bit is
complemented, together with a relabelling of rows, columns and coefficient bits. A compact basis
change along `w + e_x` (with `w_x = 0`), a reversal, the same basis change and a reversal
translate every active column by `w` (`Layer.encZ_translate`), at linear cost and without child
calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section

theorem length_encZ' (A : ℕ) {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).length = R * 2 ^ n * r * w := by
  rw [encZ, length_flatMap_const _ w (fun z => by simp [coeffSyms]), length_coeffList]

/-! ### Reversing a wire -/

section Reverse

variable {BReg : Type} [Fintype BReg] [DecidableEq BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- Reverse wire `fw` in place through its temporary and the spare. -/
def revW (fw : NWire) : Pr P (nT BReg) Q A U :=
  .seq (moveR (reg (.wire fw)) (reg (.wtmp fw)) id)
    (.seq (moveR (reg (.wtmp fw)) (reg .tmp) id) (moveR (reg .tmp) (reg (.wire fw)) id))

omit [DecidableEq BReg] in
/-- `revW`: wire `fw` goes from the stream of `Z` to the stream of `zrev w Z`; every other register
ends as it started. -/
theorem revW_exec {R r n w : ℕ} (fw : NWire) (Z : ZArr (Fin R × Fin r) n)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (htmp : S.R (reg .tmp) = []) (hwt : S.R (reg (.wtmp fw)) = [])
    (hx : S.R (reg (.wire fw)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ 6 * (encZ A w Z).length + 6 ∧
      Exec body (revW fw) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg (.wire fw)) (encZ A w (zrev w Z)) }) := by
  have n12 : reg (BReg := BReg) (.wire fw) ≠ reg (.wtmp fw) := reg_ne (by simp)
  have n23 : reg (BReg := BReg) (.wtmp fw) ≠ reg .tmp := reg_ne (by simp)
  have n31 : reg (BReg := BReg) .tmp ≠ reg (.wire fw) := reg_ne (by simp)
  let R₁ := movedR S.R (reg (.wire fw)) (reg (.wtmp fw)) id (S.R (reg (.wire fw)))
  let R₂ := movedR R₁ (reg (.wtmp fw)) (reg .tmp) id (R₁ (reg (.wtmp fw)))
  let R₃ := movedR R₂ (reg .tmp) (reg (.wire fw)) id (R₂ (reg .tmp))
  have h1 : R₁ (reg (.wtmp fw)) = (encZ A w Z).reverse := by
    simp [R₁, movedR, hx, hwt]
  have h2 : R₂ (reg .tmp) = encZ A w Z := by
    simp only [R₂, movedR, Function.update_self, List.map_id, h1, List.reverse_reverse]
    simp [R₁, movedR, htmp]
  have h3 : R₃ = Function.update S.R (reg (.wire fw)) (encZ A w (zrev w Z)) := by
    funext k
    simp only [R₃, movedR, List.map_id, h2]
    by_cases hk1 : k = reg (.wire fw)
    · subst hk1
      rw [Function.update_self, Function.update_self, ← encZ_reverse]
      simp [R₂, R₁, movedR]
    rw [Function.update_of_ne hk1, Function.update_of_ne hk1]
    by_cases hk3 : k = reg .tmp
    · subst hk3
      rw [Function.update_self, htmp]
    rw [Function.update_of_ne hk3]
    simp only [R₂, R₁, movedR]
    by_cases hk2 : k = reg (.wtmp fw)
    · subst hk2
      simp [n23, hwt]
    rw [Function.update_of_ne hk3, Function.update_of_ne hk2, Function.update_of_ne hk2,
      Function.update_of_ne hk1]
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body (reg (.wire fw)) (reg (.wtmp fw)) n12 id v S
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg (.wtmp fw)) (reg .tmp) n23 id v₁ { S with R := R₁ }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (reg .tmp) (reg (.wire fw)) n31 id v₂
    { S with R := R₂ }
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · change 2 * (S.R (reg (.wire fw))).length + 2 + (2 * (R₁ (reg (.wtmp fw))).length + 2 +
      (2 * (R₂ (reg .tmp)).length + 2)) ≤ _
    rw [hx, h1, h2, List.length_reverse]
    omega
  · change mk v₃ { S with R := R₃ } = _
    rw [h3]

/-! ### Unit scalars -/

/-- Multiply wire `fw` by `i` through its temporary. -/
noncomputable def mulIW (fw : NWire) : Pr P (nT BReg) Q A U :=
  .seq (autoWords (fun _ : Fin 1 => reg (.wire fw)) (fun _ => reg (.wtmp fw)) (reg .st) (reg .ctr)
      (reg .tmp) (gaussAuto A ![![(0, 1)]] 1 false))
    (moveR (reg (.wtmp fw)) (reg (.wire fw)) id)

/-- `i` times an array. -/
def mulIZ {Y : Type} {n : ℕ} (Z : ZArr Y n) : ZArr Y n := fun p => ⟨0, 1⟩ * Z p

theorem encZ_mulIZ {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    encZ A w (mulIZ Z) = ((coeffList w Z).map GR.mulI).flatMap (coeffSyms A w) := by
  rw [encZ, ← coeffList_map (fun z => ⟨0, 1⟩ * z) GR.mulI (fun z => by
    simp [red, GR.mulI, Zsqrtd.re_mul, Zsqrtd.im_mul]) Z]
  rfl

omit [DecidableEq BReg] in
/-- `mulIW`: wire `fw` goes from the stream of `Z` to the stream of `i Z`; every other register
ends as it started. -/
theorem mulIW_exec (hA : 5 ≤ A) {R r n w : ℕ} (hw : 1 ≤ w) (fw : NWire)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hctr : (S.R (reg .ctr)).length = w) (htmp : S.R (reg .tmp) = [])
    (hwt : S.R (reg (.wtmp fw)) = []) (hx : S.R (reg (.wire fw)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ conjCost R n r w ∧
      Exec body (mulIW fw) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg (.wire fw)) (encZ A w (mulIZ Z)) }) := by
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, he₁, hi₁, ho₁, hl₁, hX₁, hT₁, hoth₁⟩ :=
    mulI_exec body (autoLayout_one (x := .wire fw) (y := .wtmp fw)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) (by norm_num; omega) hw hctr
      (coeffList w Z) v S rfl htmp hx
  have hS₁ : S₁ = { S with R := S₁.R } := Stacks.ext hi₁ ho₁ hl₁ rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg (.wtmp fw)) (reg (.wire fw)) (reg_ne (by simp)) id
    v₁ S₁
  have hT₁' : S₁.R (reg (.wtmp fw)) = (encZ A w (mulIZ Z)).reverse := by
    rw [hT₁, hwt, List.append_nil, encZ_mulIZ]
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  · rw [hT₁', List.length_reverse, length_encZ']
    rw [length_coeffList] at hm₁
    unfold conjCost
    nlinarith
  · rw [hS₁]
    congr 2
    funext k
    simp only [movedR, List.map_id]
    by_cases ha : k = reg (.wire fw)
    · subst ha
      rw [Function.update_self, Function.update_self, hT₁', List.reverse_reverse, hX₁,
        List.append_nil]
    rw [Function.update_of_ne ha, Function.update_of_ne ha]
    by_cases hb : k = reg (.wtmp fw)
    · subst hb; rw [Function.update_self, hwt]
    rw [Function.update_of_ne hb, hoth₁ k ha hb]

end Reverse

/-! ### Translations -/

variable {Q K : ℕ} {U P : Type}

/-- Translate every active column of wire `fw` by `w`, for a slot `x` with `w_x = 0`: two
compact basis changes along `w + e_x`, each followed by a reversal. -/
def transW (hQ : compactRuntimeStates ≤ Q) (fw : NWire) (w : BinaryWalsh.Address m) (x : Fin m) :
    Pr P (nT CompactBReg) Q (prime+K) U :=
  .seq (compactBasisW hQ fw (w + Pi.single x 1) x)
    (.seq (revW fw) (.seq (compactBasisW hQ fw (w + Pi.single x 1) x) (revW fw)))

/-- **Translation.** Wire `fw` goes from the stream of `Z` to the stream of `Z` translated by
`w` in every active column; every other register ends as it started. -/
theorem transW_exec {s : Shape} {n a₀ k ρ left right o rowCount r w j u : ℕ}
    (body : P → Pr P (nT CompactBReg) Q (prime+K) U) (hQ : compactRuntimeStates ≤ Q)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
    (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk) (hr : 0<rowCount)
    (hrecord : s.bits+1 ≤ s.payload) (hA : 4 ≤ prime+K)
    (hpayload : s.payload=2^o*(3*(r*w))) (D : ℕ)
    (hp : ∀ y (hxy : x≠y),1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) D)
    (fw : NWire) (tv : BinaryWalsh.Address m) (htv : tv x = 0)
    (Z : ZArr (Fin rowCount × Fin r) (o+n))
    (v : HS (nT CompactBReg) Q (prime+K) U) (S : Stacks (nT CompactBReg) (prime+K))
    (hL : ∀ z,S.L z=[])
    (hpar : ParState S.R j u s.chunk ρ (o+a₀) (s.chunk*k) rowCount (o+n) w (r*w))
    (hbc : ∀ z,compactBasisRest s o r z (S.R (reg (.bc z))))
    (htmp : S.R (reg .tmp)=[]) (hwt : S.R (reg (.wtmp fw)) = [])
    (hstream : S.R (reg (.wire fw))=encZ (prime+K) w Z) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ 2 * (((basisTargets (tv + Pi.single x 1) x).map
        (compactBasisTargetCost layout x hG hGK hr hrecord D hp (nT CompactBReg) K o r w)).sum+1) +
          2 * (6 * (rowCount * 2 ^ (o+n) * r * w) + 6) ∧
      Exec body (transW hQ fw tv x) (mk v S) steps
        (mk v' {S with R:=Function.update S.R (reg (.wire fw)) (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (fun t => t + tv) Z))}) := by
  set e := compactOffsetEmbedding o (compactRecursiveBits layout)
  have he : Function.Injective e :=
    compactOffsetEmbedding_injective o (compactRecursiveBits_injective layout)
  have hv : (tv + Pi.single x 1 : BinaryWalsh.Address m) x = 1 := by simp [htv]
  set B := basisMap (tv + Pi.single x 1) x
  have hw : reg (BReg := CompactBReg) (.wire fw) ∉ parRegs.map reg := by simp [parRegs]
  have hpar' : ∀ R', (∀ z, z ≠ reg (.wire fw) → R' z = S.R z) →
      ParState R' j u s.chunk ρ (o+a₀) (s.chunk*k) rowCount (o+n) w (r*w) := fun R' hR' =>
    hpar.congr fun y hy => hR' _ (fun h => hw (h ▸ List.mem_map_of_mem hy))
  -- step 1
  obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := compactBasisW_exec body hQ layout x hG hGK hr hrecord hA
    hpayload D hp fw (tv + Pi.single x 1) hv Z v S hL hpar hbc htmp hstream
  set S₁ : Stacks (nT CompactBReg) (prime+K) :=
    {S with R := (Function.update S.R (reg (.wire fw)) (encZ (prime+K) w (pullM e B Z)))}
  have hS₁ : ∀ z, z ≠ reg (.wire fw) → S₁.R z = S.R z := fun z hz => Function.update_of_ne hz _ _
  -- step 2
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := revW_exec body fw (pullM e B Z) v₁ S₁
    ((hS₁ _ (reg_ne (by simp))).trans htmp) ((hS₁ _ (reg_ne (by simp))).trans hwt)
    (Function.update_self _ _ _)
  set S₂ : Stacks (nT CompactBReg) (prime+K) :=
    {S with R := (Function.update S.R (reg (.wire fw)) (encZ (prime+K) w (zrev w (pullM e B Z))))}
  have e₂ : ({S₁ with R := (Function.update S₁.R (reg (.wire fw))
      (encZ (prime+K) w (zrev w (pullM e B Z))))} : Stacks (nT CompactBReg) (prime+K)) = S₂ := by
    simp only [S₁, S₂, Function.update_idem]
  rw [e₂] at he₂
  have hS₂ : ∀ z, z ≠ reg (.wire fw) → S₂.R z = S.R z := fun z hz => Function.update_of_ne hz _ _
  -- step 3
  obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := compactBasisW_exec body hQ layout x hG hGK hr hrecord hA
    hpayload D hp fw (tv + Pi.single x 1) hv (zrev w (pullM e B Z)) v₂ S₂ hL (hpar' _ hS₂)
    (fun z => by rw [hS₂ _ (reg_ne (by simp))]; exact hbc z)
    ((hS₂ _ (reg_ne (by simp))).trans htmp) (Function.update_self _ _ _)
  set S₃ : Stacks (nT CompactBReg) (prime+K) :=
    {S with R := (Function.update S.R (reg (.wire fw))
      (encZ (prime+K) w (pullM e B (zrev w (pullM e B Z)))))}
  have e₃ : ({S₂ with R := (Function.update S₂.R (reg (.wire fw))
      (encZ (prime+K) w (pullM e B (zrev w (pullM e B Z)))))} : Stacks (nT CompactBReg) (prime+K)) =
        S₃ := by
    simp only [S₂, S₃, Function.update_idem]
  rw [e₃] at he₃
  have hS₃ : ∀ z, z ≠ reg (.wire fw) → S₃.R z = S.R z := fun z hz => Function.update_of_ne hz _ _
  -- step 4
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := revW_exec body fw (pullM e B (zrev w (pullM e B Z))) v₃ S₃
    ((hS₃ _ (reg_ne (by simp))).trans htmp) ((hS₃ _ (reg_ne (by simp))).trans hwt)
    (Function.update_self _ _ _)
  refine ⟨v₄, c₁ + (c₂ + (c₃ + c₄)), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl ?_)))⟩
  · rw [length_encZ'] at hc₂ hc₄
    omega
  · simp only [S₃, Function.update_idem]
    rw [encZ_translate he]
    exact htv

end

end IntegerMultBounds.MathlibTM2.LayerMachine
