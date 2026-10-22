module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBlank
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame

/-! Every R2 scratch and installed destination lies off its record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

theorem SelectiveHost.Valid.blank_src {T : ℕ} {H : SelectiveHost T} (hH : H.Valid)
    (j : Fin T) (hj : H.Blank j) : j ≠ H.src := by
  intro he
  subst j
  rcases hj with hm | ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨off, r, _, _, hr⟩ | ⟨c, r, _, hr⟩
  · have hn := (List.nodup_cons.mp (hH.move .A).regs).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h
    · exact hn (by simp [h])
    · exact hn (by simp [h])
    · exact hn (by simp [h])
  · exact (hH.move .A).dst_regs d (by simp [hd])
  · exact (hH.move .A).aux_regs d (by simp [hd])
  · exact SelectiveHost.Valid.cb_src H hH off r hr
  · exact hH.swap_src c r hr

theorem repairBlank_src (j : Fin repairT) (hj : RepairBlank j) : j ≠ repairHost.src := by
  rcases hj with hh | he | ⟨r, _, _, _, hr⟩ | ⟨r, _, _, _, _, hr⟩
  · exact repairHost_valid.blank_src j hh
  · rw [he]; simp
  · rw [← hr]; exact repairKey_src r
  · rw [← hr]; exact repairBad_src r

theorem repairBlank_updateStream {A : ℕ} (R : Fin repairT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (hblank : ∀ j, RepairBlank j → R j = []) :
    ∀ j, RepairBlank j → Function.update R repairHost.src out j = [] := by
  intro j hj
  rw [Function.update_of_ne (repairBlank_src j hj)]
  exact hblank j hj

end IntegerMultBounds.MathlibTM2.Routing
