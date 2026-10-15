module

public import IntegerMultBounds.MathlibTM2.Fast.CRTMachine
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! # Backing registers for the direct CRT machines

The seven persistent legacy parameters keep their old names. All other direct
external slots and all table-bank registers use entries of `crtRestEmpty`.
The old scan-state and carry registers are deliberately outside this backing.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open TableVM

/-- Forty external slots followed by the twenty-five-register table bank. -/
def crtDirectBackingNames : List CrtReg :=
  [
    .str, .extra 0, .extra 1, .extra 2, .extra 3, .extra 4, .extra 5, .extra 6,
    .msk, .extra 7, .extra 8, .zr, .extra 9, .extra 10, .extra 11, .extra 12,
    .extra 13, .extra 14, .extra 15, .extra 16, .extra 17, .extra 18, .extra 19, .extra 20,
    .extra 21, .extra 22, .extra 23, .extra 24, .extra 25, .extra 26, .extra 27, .wT,
    .sT, .mT, .extra 28, .extra 29, .extra 30, .extra 31, .sig, .acc,
    .tA, .tB, .tc, .tr, .u1, .u2, .bU, .wD,
    .sD, .mD, .wW, .aI, .sI, .muI, .aK, .preU,
    .postU, .uU, .vU, .vacc, .e3B, .t3B, .tu, .stmp,
    .rbU]

lemma crtDirectBackingNames_length : crtDirectBackingNames.length = 65 := by decide

lemma crtDirectBackingNames_nodup : crtDirectBackingNames.Nodup := by decide

def crtDirectBacking (i : Fin 65) : CrtReg :=
  crtDirectBackingNames.get ⟨i.val, by rw [crtDirectBackingNames_length]; exact i.isLt⟩

lemma crtDirectBacking_injective : Function.Injective crtDirectBacking := by
  intro i j h
  have he := crtDirectBackingNames_nodup.injective_get h
  exact Fin.ext (congrArg Fin.val he)

/-- External-slot backing, preserving the legacy data and parameter aliases. -/
def crtDirectExternal (i : Fin 40) : CrtReg := crtDirectBacking (Fin.castAdd 25 i)

lemma crtDirectExternal_injective : Function.Injective crtDirectExternal := by
  intro i j h
  have he := crtDirectBacking_injective h
  exact Fin.ext (congrArg (fun k : Fin 65 => k.val) he)

/-- An explicit table-bank index, independent of any global finite enumeration. -/
def crtDirectBankIndex : TblR 10 → Fin 25
  | .v i => ⟨i.val, by omega⟩
  | .wr => 10
  | .wn => 11
  | .acc => 12
  | .z j => ⟨13 + j.val, by omega⟩

lemma crtDirectBankIndex_injective : Function.Injective crtDirectBankIndex := by
  intro x y h
  cases x <;> cases y <;> simp [crtDirectBankIndex, Fin.ext_iff] at h ⊢ <;> omega

/-- Table-bank backing uses the final twenty-five entries. -/
def crtDirectBank (q : TblR 10) : CrtReg :=
  crtDirectBacking ⟨40 + (crtDirectBankIndex q).val, by have := (crtDirectBankIndex q).isLt; omega⟩

lemma crtDirectBank_injective : Function.Injective crtDirectBank := by
  intro x y h
  have he := congrArg Fin.val (crtDirectBacking_injective h)
  apply crtDirectBankIndex_injective
  apply Fin.ext
  simpa using he

lemma crtDirectBank_ne_external (q : TblR 10) (i : Fin 40) :
    crtDirectBank q ≠ crtDirectExternal i := by
  intro h
  have he := congrArg Fin.val (crtDirectBacking_injective h)
  have := i.isLt
  simp only [Fin.val_castAdd] at he
  omega

@[simp] lemma crtDirectExternal_str : crtDirectExternal 0 = .str := rfl
@[simp] lemma crtDirectExternal_msk : crtDirectExternal 8 = .msk := rfl
@[simp] lemma crtDirectExternal_zr : crtDirectExternal 11 = .zr := rfl
@[simp] lemma crtDirectExternal_wT : crtDirectExternal 31 = .wT := rfl
@[simp] lemma crtDirectExternal_sT : crtDirectExternal 32 = .sT := rfl
@[simp] lemma crtDirectExternal_mT : crtDirectExternal 33 = .mT := rfl
@[simp] lemma crtDirectExternal_sig : crtDirectExternal 38 = .sig := rfl

/-- Every external slot other than the seven persistent parameters is empty
under the existing source-stage rest contract. -/
lemma crtDirectExternal_mem_rest (i : Fin 40) (h0 : i ≠ 0) (h8 : i ≠ 8) (h11 : i ≠ 11)
    (h31 : i ≠ 31) (h32 : i ≠ 32) (h33 : i ≠ 33) (h38 : i ≠ 38) :
    crtDirectExternal i ∈ crtRestEmpty := by
  fin_cases i <;> simp_all [crtDirectExternal, crtDirectBacking, crtDirectBackingNames,
    crtRestEmpty, crtIdle]

lemma crtDirectBank_mem_rest (q : TblR 10) : crtDirectBank q ∈ crtRestEmpty := by
  cases q with
  | v i => fin_cases i <;> decide
  | wr => decide
  | wn => decide
  | acc => decide
  | z j => fin_cases j <;> decide

end IntegerMultBounds.MathlibTM2.Fast
