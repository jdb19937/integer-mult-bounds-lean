module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Wrapper
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRoot

/-!
# Array moves and the stage-1 transpose

The supplier's interface states its output as `Shared50RecursiveNodeRows.transpose`, the H/D
transpose of a bit array; the wrapper's steps are array moves (`Stage2Wrapper.Moves`) on the
zero extension of the array. The two agree: the transpose moves the record at `(h, d)` to
`(d, h)` (`transpose_moves`), and an array whose move is the swap is the transpose
(`eq_transpose`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Transpose

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume index)
open RecursiveInterchangeRows (pack suffixIndex)
open Stage2Wrapper (Moves)
open FamilyRoot (ext)

variable {v : Descriptor}

theorem ext_lt {V : ℕ} (x : Fin V → ZMod 2) (z : Fin V) : ext x z = x z := by
  simp [ext]

/-- The address of a record of `v`. -/
def addr (a : Fin v.beforeRows) (row : Fin v.rows) (before : Fin v.beforeH) (h : Fin (prime ^ v.width))
    (mid : Fin v.between) (d : Fin (prime ^ v.width)) (after : Fin v.afterD) : Fin (volume prime v) :=
  Fin.cast (RecursiveInterchangeRows.volume_split prime 1 v (one_dvd v.rows)).symm
    (pack (pack a (Fin.cast (Nat.div_one v.rows).symm row)) (pack (0 : Fin 1) (suffixIndex prime v before h mid d after)))

theorem addr_val (a : Fin v.beforeRows) (row : Fin v.rows) (before : Fin v.beforeH) (h : Fin (prime ^ v.width))
    (mid : Fin v.between) (d : Fin (prime ^ v.width)) (after : Fin v.afterD) :
    (addr a row before h mid d after).val = index prime v a row before h mid d after := by
  have := RecursiveInterchangeRows.cyclic_index prime 1 v (one_dvd v.rows) a
    (Fin.cast (Nat.div_one v.rows).symm row) 0 before h mid d after
  simpa [addr] using this

/-- Every record has an address. -/
theorem addr_surj (z : Fin (volume prime v)) : ∃ a row before h mid d after,
    z = addr (v := v) a row before h mid d after := by
  set z' := Fin.cast (RecursiveInterchangeRows.volume_split prime 1 v (one_dvd v.rows)) z
  obtain ⟨⟨g, r⟩, hg⟩ : ∃ p, finProdFinEquiv p = z' := ⟨_, finProdFinEquiv.apply_symm_apply z'⟩
  obtain ⟨⟨a, row⟩, ha⟩ : ∃ p, finProdFinEquiv p = g := ⟨_, finProdFinEquiv.apply_symm_apply g⟩
  obtain ⟨⟨j, k⟩, hj⟩ : ∃ p, finProdFinEquiv p = r := ⟨_, finProdFinEquiv.apply_symm_apply r⟩
  have hj0 : j = 0 := Subsingleton.elim _ _
  set s := Shared50RecursiveNodeRows.suffixUnpack k
  refine ⟨a, Fin.cast (Nat.div_one v.rows) row, s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2, ?_⟩
  apply Fin.ext
  have hk : Shared50RecursiveNodeRows.suffixPack s = k := Shared50RecursiveNodeRows.suffixPack_unpack k
  have hz : z = Fin.cast (RecursiveInterchangeRows.volume_split prime 1 v (one_dvd v.rows)).symm z' := by
    simp [z']
  rw [hz, addr]
  congr 2
  rw [← hg, ← ha, ← hj, hj0]
  change pack (pack a row) (pack 0 k) = pack (pack a (Fin.cast _ (Fin.cast _ row))) (pack 0 (Shared50RecursiveNodeRows.suffixPack s))
  rw [hk]
  rfl

theorem transpose_addr (x : Fin (volume prime v) → ZMod 2) (a : Fin v.beforeRows) (row : Fin v.rows)
    (before : Fin v.beforeH) (h : Fin (prime ^ v.width)) (mid : Fin v.between) (d : Fin (prime ^ v.width))
    (after : Fin v.afterD) :
    Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x (addr a row before h mid d after) =
      x (addr a row before d mid h after) := by
  have := Shared50RecursiveNodeRows.transpose_entry (one_dvd v.rows) x
    (pack a (Fin.cast (Nat.div_one v.rows).symm row)) 0 (suffixIndex prime v before h mid d after)
  change _ = x (Fin.cast _ (pack _ (pack 0 (Shared50RecursiveNodeRows.suffixPack (before, d, mid, h, after)))))
  rw [← Shared50RecursiveNodeRows.swapSuffix_pack]
  exact this

/-- **The transpose is the move of the swap.** -/
theorem transpose_moves (x : Fin (volume prime v) → ZMod 2) :
    Moves prime v Prod.swap (ext x) (ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) := by
  intro a ha row hrow before hb h hh mid hm d hd after haf
  have e₁ := addr_val (v := v) ⟨a, ha⟩ ⟨row, hrow⟩ ⟨before, hb⟩ ⟨d, hd⟩ ⟨mid, hm⟩ ⟨h, hh⟩ ⟨after, haf⟩
  have e₂ := addr_val (v := v) ⟨a, ha⟩ ⟨row, hrow⟩ ⟨before, hb⟩ ⟨h, hh⟩ ⟨mid, hm⟩ ⟨d, hd⟩ ⟨after, haf⟩
  simp only [Prod.swap_prod_mk]
  rw [← e₁, ← e₂, ext_lt, ext_lt]
  exact transpose_addr x _ _ _ _ _ _ _

/-- **An array whose move is the swap is the transpose.** -/
theorem eq_transpose {x y : Fin (volume prime v) → ZMod 2} (hm : Moves prime v Prod.swap (ext x) (ext y)) :
    y = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  funext z
  obtain ⟨a, row, before, h, mid, d, after, rfl⟩ := addr_surj z
  rw [transpose_addr]
  have := hm a a.isLt row row.isLt before before.isLt d d.isLt mid mid.isLt h h.isLt after after.isLt
  simp only [Prod.swap_prod_mk] at this
  rw [← addr_val, ← addr_val, ext_lt, ext_lt] at this
  exact this

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Transpose
