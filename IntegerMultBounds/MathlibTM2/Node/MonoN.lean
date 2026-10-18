module

public import IntegerMultBounds.MathlibTM2.Node.Mono

/-! **The exact instructions on the slot-XOR register file.** A slot XOR is the basis change
`basisW` along `e_i + e_j` at the pivot `i`; a translation by `w` with `w_x = 0` is the basis change
along `w + e_x`, a reversal, the same basis change and a reversal (`Layer.encZ_translate`); both run
framed at the parameters of the child level. A slot phase is `phaseInstr`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

section MonoN

variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q (prime + Ka) U)

/-- The translation of wire `fw` by `tv` with `tv x = 0`. -/
def transWN (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (fw : NWire) (tv : BinaryWalsh.Address m)
    (x : Fin m) : Pr P (nT SXReg) Q (prime + Ka) U :=
  .seq (basisW hQ fw (tv + Pi.single x 1) x)
    (.seq (revW fw) (.seq (basisW hQ fw (tv + Pi.single x 1) x) (revW fw)))

/-- The program of an exact instruction. -/
def monoProgN (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) : Instr → Pr P (nT SXReg) Q (prime + Ka) U
  | .trans fw tv => if h : ∃ x, tv x = 0 then framed (transWN hQ fw tv (Fin.find _ h)) else .act .done
  | .xor fw i j => framed (basisW hQ fw (Pi.single i 1 + Pi.single j 1) i)
  | .phase fw i c => phaseInstr fw i c
  | _ => .act .done

/-- The step bound of the program of an exact instruction at level `j + 1`. -/
def monoCostN (T : ℕ) (j u K ρ a₀ R₀ n r w : ℕ) : Instr → ℕ
  | .trans _ tv => if h : ∃ x, tv x = 0 then framedCost j u K R₀
      (2 * basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j)
        (tv + Pi.single (Fin.find _ h) 1) (Fin.find _ h) +
        2 * (6 * (rowsAt R₀ j * 2 ^ n * r * w) + 6)) else 1
  | .xor _ i j' => framedCost j u K R₀
      (basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j)
        (Pi.single i 1 + Pi.single j' 1) i)
  | .phase _ _ _ => phaseInstrCost u j a₀ ρ K (rowsAt R₀ j) n r w
  | _ => 1

/-- The basis change on a framed wire. -/
theorem basisW_framed (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hA : 14 ≤ prime + Ka)
    {j u K ρ a₀ R₀ n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n) (hfitL : a₀ + K * bits u (j + 1) ≤ n)
    (fw : NWire) (vv : BinaryWalsh.Address m) (s : Fin m) (hvs : vv s = 1)
    (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka))
    (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ (K * bits u j) (rowsAt R₀ j) n w (r * w))
    (hrest : RestBut bcEmpty n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) S.R)
    (hx : S.R (reg (.wire fw)) = encZ (prime + Ka) w Z) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ basisCostN (nT SXReg) a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) vv s ∧
      Exec body (basisW hQ fw vv s) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire fw))
          (encZ (prime + Ka) w (pullM (actMap a₀ ρ K (bits u (j + 1)) n hfit) (basisMap vv s) Z)) }) :=
  basisW_exec body hQ hA (k := bits u j) hρ rfl (bits_pos hu j) (rowsAt_pos hR₀ j)
    (Nat.mul_pos hr hw) (by rw [show K * bits u (j + 1) = m * (K * bits u j) by
      rw [show bits u (j + 1) = m * bits u j from rfl]; ring] at hfitL; exact hfitL)
    (fun _ => rfl) fw vv s hvs Z v S hL hx (hpar .K) (hpar .ρ) (hpar .a₀) (hpar .L) (hpar .rows)
    (hpar .n) (hpar .rw) (fun y => hrest (.bc y) (by simp))

/-- **The exact instructions on the slot-XOR register file.** -/
theorem monoProgN_spec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hA : 14 ≤ prime + Ka)
    {j u K ρ a₀ R₀ n r w Tc : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hu : 1 ≤ u)
    (hR₀ : 1 ≤ R₀) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfitL : a₀ + K * bits u (j + 1) ≤ n)
    (child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (ins : Instr) (hfit' : ins.Fit) (hmono : ins.IsMono) :
    MonoSpecL body (monoProgN hQ ins) bcEmpty j u K ρ a₀ (K * bits u (j + 1)) (rowsAt R₀ (j + 1))
      n r w (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit) child Tc ins
      (monoCostN (nT SXReg) j u K ρ a₀ R₀ n r w ins) := by
  have hK : 1 ≤ K := by omega
  set e := actMap a₀ ρ K (bits u (j + 1)) n hfit with he
  have hinj : Function.Injective e := actMap_injective hK hfit
  cases ins with
  | factor fw g => exact absurd hmono id
  | gate g => exact absurd hmono id
  | phase fw i c => exact phaseInstr_monoSpecL body (by omega) hr hw hK hfit child fw i c
  | xor fw i j' =>
    have hij : i ≠ j' := hfit'
    refine framed_spec body _ fw e child _ (pullM e (Networks.Certificates.T16.Impl.xorMap i j'))
      _ (fun B => rfl) fun v S Z hL hpar hrest hx => ?_
    obtain ⟨v', c, hu', hc, hex⟩ := basisW_framed body hQ hA hr hw hρ hu hR₀ hfit hfitL fw _ i
      (xor_pivot hij) v S Z hL hpar hrest hx
    rw [basisMap_xor hij] at hex
    exact ⟨v', c, hu', hc, hex⟩
  | trans fw tv =>
    have h : ∃ x, tv x = 0 := hfit'
    simp only [monoProgN, monoCostN, h, ↓reduceDIte]
    set x := Fin.find _ h with hxdef
    have hx0 : tv x = 0 := Fin.find_spec h
    have hv : (tv + Pi.single x 1 : BinaryWalsh.Address m) x = 1 := by simp [hx0]
    refine framed_spec body _ fw e child _ (pullM e (fun t => t + tv)) _ (fun B => rfl)
      fun v S Z hL hpar hrest hZ => ?_
    have htmp : S.R (reg .tmp) = [] := hrest .tmp (by simp)
    have hwt : S.R (reg (.wtmp fw)) = [] := hrest (.wtmp fw) (by simp)
    set B₁ := basisMap (tv + Pi.single x 1) x
    obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := basisW_framed body hQ hA hr hw hρ hu hR₀ hfit hfitL fw _ x
      hv v S Z hL hpar hrest hZ
    have hS₁ : ∀ q, q ≠ reg (.wire fw) →
        (Function.update S.R (reg (.wire fw)) (encZ (prime + Ka) w (pullM e B₁ Z))) q = S.R q :=
      fun q hq => Function.update_of_ne hq _ _
    obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := revW_exec body fw (pullM e B₁ Z) v₁
      { S with R := Function.update S.R (reg (.wire fw)) (encZ (prime + Ka) w (pullM e B₁ Z)) }
      ((hS₁ _ (reg_ne (by simp))).trans htmp) ((hS₁ _ (reg_ne (by simp))).trans hwt)
      (Function.update_self _ _ _)
    simp only [Function.update_idem] at he₂
    set S₂ : Stacks (nT SXReg) (prime + Ka) := { S with R := (Function.update S.R (reg (.wire fw))
      (encZ (prime + Ka) w (zrev w (pullM e B₁ Z)))) }
    have hS₂ : ∀ q, q ≠ reg (.wire fw) → S₂.R q = S.R q := fun q hq => Function.update_of_ne hq _ _
    obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := basisW_framed body hQ hA hr hw hρ hu hR₀ hfit hfitL fw _ x
      hv v₂ S₂ (zrev w (pullM e B₁ Z)) hL (hpar.congr fun y hy => hS₂ _ (reg_ne fun h' =>
        (parRegs_ne hy).2.1 fw h'))
      (hrest.congr fun y hy => hS₂ _ (reg_ne fun h' => hy (Or.inl ⟨fw, h'⟩)))
      (Function.update_self _ _ _)
    simp only [S₂, Function.update_idem] at he₃
    set S₃ : Stacks (nT SXReg) (prime + Ka) := { S with R := (Function.update S.R (reg (.wire fw))
      (encZ (prime + Ka) w (pullM e B₁ (zrev w (pullM e B₁ Z))))) }
    have hS₃ : ∀ q, q ≠ reg (.wire fw) → S₃.R q = S.R q := fun q hq => Function.update_of_ne hq _ _
    obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := revW_exec body fw (pullM e B₁ (zrev w (pullM e B₁ Z))) v₃ S₃
      ((hS₃ _ (reg_ne (by simp))).trans htmp) ((hS₃ _ (reg_ne (by simp))).trans hwt)
      (Function.update_self _ _ _)
    simp only [S₃, Function.update_idem] at he₄
    refine ⟨v₄, c₁ + (c₂ + (c₃ + c₄)), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
      Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl ?_)))⟩
    · rw [length_encZ'] at hc₂ hc₄
      omega
    · rw [encZ_translate hinj _ _ tv x hx0]

end MonoN

end

end IntegerMultBounds.MathlibTM2.LayerMachine
