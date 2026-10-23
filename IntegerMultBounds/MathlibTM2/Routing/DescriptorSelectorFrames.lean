module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorTableCompile
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite

/-! Exact framing and price for serializing live binary selectors. The source
register list is code; selector values and widths are read from the live bank.
This is the emission interface, not the sparse-profile coordinate generator. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A M : ℕ} {P U : Type}

theorem descriptorSelectorFrames_append (L : ℕ) (qs rs : List (Fin M)) :
    descriptorSelectorFrames (A := A) L (qs ++ rs) =
      descriptorSelectorFrames L qs ++ descriptorSelectorFrames L rs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [descriptorSelectorFrames, ih, List.append_assoc]

theorem configurationWords_binSyms (L : ℕ) (qs : List (Fin M)) :
    configurationWords (qs.map (fun q => (binSyms L q.val : List (Fin (A + 4))))) =
      descriptorSelectorFrames L qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [configurationWords, descriptorSelectorFrames, ih]

theorem descriptorSelectorWrite_exec (body : P → Pr P T Q A U)
    (dst tmp work : Fin T) (hreg : [dst, tmp, work].Nodup)
    (fields : List (Fin T)) (qs : List (Fin M)) (L : ℕ)
    (hfields : ∀ src ∈ fields, src ≠ dst ∧ src ≠ tmp ∧ src ≠ work)
    (v : HS T Q A U) (S : Stacks T A)
    (hvalues : fields.map S.R = qs.map (fun q => binSyms L q.val))
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationWrite dst tmp work fields) (mk v S)
        (qs.length * (6 * L + 7) + 1)
        (mk v' { S with R := Function.update S.R dst (descriptorSelectorFrames L qs ++ S.R dst) }) := by
  obtain ⟨v', hu, he⟩ := configurationWrite_exec body dst tmp work hreg fields hfields v S htmp hwork
  have hcost : configurationWriteCost S.R fields = qs.length * (6 * L + 7) + 1 := by
    have hlen : fields.length = qs.length := by
      have hv := congrArg List.length hvalues
      simpa using hv
    have hwidth : ∀ src ∈ fields, (S.R src).length = L := by
      intro src hs
      have hm : S.R src ∈ qs.map (fun q => binSyms L q.val) := by
        rw [← hvalues]; exact List.mem_map.mpr ⟨src, hs, rfl⟩
      obtain ⟨q, _, hq⟩ := List.mem_map.mp hm
      rw [← hq, length_binSyms]
    have hc : ∀ fs : List (Fin T), (∀ src ∈ fs, (S.R src).length = L) →
        configurationWriteCost S.R fs = fs.length * (6 * L + 7) + 1 := by
      intro fs hw
      induction fs with
      | nil => simp [configurationWriteCost]
      | cons src fs ih =>
        simp only [configurationWriteCost, List.length_cons]
        rw [hw src (by simp), ih (fun x hx => hw x (by simp [hx]))]
        simp [Nat.add_mul]; omega
    rw [hc fields hwidth, hlen]
  rw [hvalues, configurationWords_binSyms, hcost] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
