module

public import IntegerMultBounds.MathlibTM2.Fast.SynFwd
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGen

/-!
# The registers of the layout programs of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. The layout programs `slyFwd`, `slyOpp`
(`Fast/SynLayFwd.lean`, `Fast/SynLayOpp.lean`) run the layout machine of `Fast/Layout.lean`, its
loaders (`Fast/LoadLayout.lean`) and the writer of the description streams
(`Fast/LoadLayoutHost.lean`) on the register file of the layer machine.

## Register maps

* `slyRg : LayReg 6 → Fin (nT CReg)`: the record stream `str` is `io` itself, the interchange
  bank is the bank `swp 0` of the layer machine, every other register is the layout wire `ly i`
  of `synLayRg`.
* `slyT c` (`c < 64`): the temporaries `wtmp (wireOf c)` of the bank of the layer machine, empty
  whenever a transform runs (`synIdle`).
* `slyLr : LdlReg → Fin (nT CReg)`: the loader registers on `slyT 0 … slyT 6`.
* `slyGr : LdgReg → Fin (nT CReg)`: the writer's unary inputs `N, ℓ, K, D` are the persistent
  wires `p .N`, `p .ℓ`, `p .K`, `p .D` (read only), `B` is `s 0`, the axis word `E` is `s 2`, the
  word width register `wr` of the table machine is `s 1`; the other table registers and the spare
  `tc` are on `slyT 7 … slyT 61`.

`sly_regs : LdgRegs slyRg slyLr slyGr`; `sly_swapT : swapT 6 ≤ nT CReg`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

/-! ### The temporaries -/

theorem sly_NW : 64 ≤ NW := by rw [IntegerMultBounds.MathlibTM2.Cost.br_NW_eq]; norm_num

/-- The temporary `c` of the layout programs: the bank temporary of wire `c`. -/
noncomputable def slyT (c : Fin 64) : Fin (nT CReg) :=
  reg (BReg := CReg) (.wtmp (wireOf (Fin.castLE sly_NW c)))

@[simp] theorem slyT_inj {a b : Fin 64} : slyT a = slyT b ↔ a = b := by
  constructor
  · intro h
    simp only [slyT, reg_inj, LReg.wtmp.injEq] at h
    exact Fin.castLE_injective sly_NW (wireOf.injective h)
  · rintro rfl; rfl

theorem slyT_ne_sreg (x : SynW) (c : Fin 64) : sreg x ≠ slyT c := by
  simp [slyT, sreg_eq]

theorem slyT_out (c : Fin 64) : ∀ x, sreg x ≠ slyT c := fun x => slyT_ne_sreg x c

@[simp] theorem sreg_eq_slyT_iff (x : SynW) (c : Fin 64) : sreg x = slyT c ↔ False :=
  ⟨slyT_ne_sreg x c, False.elim⟩

@[simp] theorem slyT_eq_sreg_iff (x : SynW) (c : Fin 64) : slyT c = sreg x ↔ False :=
  ⟨fun h => slyT_ne_sreg x c h.symm, False.elim⟩

/-! ### The register maps -/

/-- The layout registers: `str` is `io`, the bank is `swp 0`, the others are the wires
`ly i`. -/
noncomputable def slyRg : LayReg 6 → Fin (nT CReg)
  | .str => reg (BReg := CReg) .io
  | .r0 => sreg (.ly 1)
  | .r1 => sreg (.ly 2)
  | .r2 => sreg (.ly 3)
  | .r3 => sreg (.ly 4)
  | .q0 => sreg (.ly 5)
  | .q1 => sreg (.ly 6)
  | .q2 => sreg (.ly 7)
  | .q3 => sreg (.ly 8)
  | .ctrB => sreg (.ly 9)
  | .cnt => sreg (.ly 10)
  | .tmp => sreg (.ly 11)
  | .st => sreg (.ly 12)
  | .fld => sreg (.ly 13)
  | .mA => sreg (.ly 14)
  | .mB => sreg (.ly 15)
  | .us r => sreg (.ly ⟨16 + r.val, by omega⟩)
  | .sw j => reg (BReg := CReg) (.bc (.inl (.sx (.swp 0 j))))
  | .cM => sreg (.ly 19)
  | .tM => sreg (.ly 20)
  | .cX => sreg (.ly 21)
  | .tX => sreg (.ly 22)

/-- The loader registers. -/
noncomputable def slyLr : LdlReg → Fin (nT CReg)
  | .dM => slyT 0
  | .dX => slyT 1
  | .cN => slyT 2
  | .cW => slyT 3
  | .tA => slyT 4
  | .tB => slyT 5
  | .tS => slyT 6

/-- The registers of the writer. -/
noncomputable def slyGr : LdgReg → Fin (nT CReg)
  | .tbl (.v i) => slyT ⟨8 + i.val, by omega⟩
  | .tbl .wr => sreg (.s 1)
  | .tbl .wn => slyT 48
  | .tbl .acc => slyT 49
  | .tbl (.z j) => slyT ⟨50 + j.val, by omega⟩
  | .uN => sreg (.p .N)
  | .uL => sreg (.p .ℓ)
  | .uK => sreg (.p .K)
  | .uD => sreg (.p .D)
  | .uB => sreg (.s 0)
  | .eW => sreg (.s 2)
  | .tc => slyT 7

theorem slyRg_injective : Function.Injective slyRg := by
  intro x y h
  cases x <;> cases y <;> simp only [slyRg, sreg_eq, reg_inj, LReg.wire.injEq,
    synWire_eq_iff, SynW.ly.injEq, LReg.bc.injEq, Sum.inl.injEq, CXReg.sx.injEq, SXReg.swp.injEq, reduceCtorEq, true_and,
    LayReg.us.injEq, LayReg.sw.injEq] at h ⊢ <;>
    first
    | rfl
    | exact h
    | (simp only [Fin.ext_iff, Fin.val_ofNat] at h; omega)

theorem slyLr_injective : Function.Injective slyLr := by
  intro x y h
  cases x <;> cases y <;> simp only [slyLr, slyT_inj] at h ⊢ <;>
    first | rfl | (simp only [Fin.ext_iff, Fin.val_ofNat] at h; omega)

theorem slyGr_injective : Function.Injective slyGr := by
  intro x y h
  rcases x with ((i | _ | _ | _ | j)) | _ | _ | _ | _ | _ | _ | _ <;>
  rcases y with ((i' | _ | _ | _ | j')) | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [slyGr, slyT_inj, sreg_eq_slyT_iff, slyT_eq_sreg_iff,
      sreg_injective.eq_iff, SynW.s.injEq, SynW.p.injEq, reduceCtorEq,
      LdgReg.tbl.injEq, TblR.v.injEq, TblR.z.injEq] at h ⊢ <;>
    first | rfl | (exact absurd h (by decide)) |
      (simp only [Fin.ext_iff, Fin.val_ofNat] at h ⊢; omega)

theorem slyRg_slyLr (x : LayReg 6) (y : LdlReg) : slyRg x ≠ slyLr y := by
  cases x <;> cases y <;> simp [slyRg, slyLr, slyT, sreg_eq]

theorem slyGr_slyRg (x : LdgReg) (y : LayReg 6) : slyGr x ≠ slyRg y := by
  rcases x with ((i | _ | _ | _ | j)) | _ | _ | _ | _ | _ | _ | _ <;> cases y <;>
    simp [slyGr, slyRg, slyT, sreg_eq]

theorem slyGr_slyLr (x : LdgReg) (y : LdlReg) : slyGr x ≠ slyLr y := by
  rcases x with ((i | _ | _ | _ | j)) | _ | _ | _ | _ | _ | _ | _ <;> cases y <;>
    simp only [slyGr, slyLr, slyT_inj, sreg_eq_slyT_iff, ne_eq, not_false_eq_true] <;>
    simp only [Fin.ext_iff, Fin.val_ofNat] <;> omega

/-- The three register maps of the layout stage. -/
theorem sly_regs : LdgRegs slyRg slyLr slyGr :=
  ⟨⟨slyRg_injective, slyLr_injective, slyRg_slyLr⟩, slyGr_injective, slyGr_slyRg, slyGr_slyLr⟩

theorem sly_swapT : swapT 6 ≤ nT CReg := by
  have h : Function.Injective fun j : Fin (swapT 6) => reg (BReg := CReg) (.bc (.inl (.sx (.swp 0 j)))) := by
    intro a b e
    simpa using e
  simpa using Fintype.card_le_of_injective _ h

theorem sly_sw_injective : Function.Injective fun j => slyRg (.sw j) :=
  fun _ _ h => by simpa using slyRg_injective h

end IntegerMultBounds.MathlibTM2.Fast
