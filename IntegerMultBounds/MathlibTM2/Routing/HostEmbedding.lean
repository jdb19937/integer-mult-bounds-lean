module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveSetup

/-! Transport the complete routing host and its setup contract to a larger bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T T' : ℕ}

def SelectiveHost.map (H : SelectiveHost T) (e : Fin T → Fin T') : SelectiveHost T' where
  cf f := e (H.cf f)
  cb off r := e (H.cb off r)
  src := e H.src
  dst d := e (H.dst d)
  aux d := e (H.aux d)
  out := e H.out
  ctr := e H.ctr
  tmp := e H.tmp
  cnt := e H.cnt
  ctmp := e H.ctmp
  swaps c j := e (H.swaps c j)

theorem SelectiveHost.Valid.map {H : SelectiveHost T} (hH : H.Valid)
    (e : Fin T → Fin T') (he : Function.Injective e) : (H.map e).Valid := by
  constructor
  · intro off
    exact ⟨he.comp (hH.callback off).fields_inj, he.comp (hH.callback off).callback_inj,
      congrArg e (hH.callback off).target,
      fun r hr f => he.ne ((hH.callback off).separate r hr f)⟩
  · intro off
    have h := hH.move off
    constructor
    · simpa only [SelectiveHost.map, List.map_cons, List.map_nil] using h.regs.map he
    · intro d hm
      have hd := h.dst_regs d
      simp only [SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false, he.eq_iff] at hm
      exact hd (by simpa using hm)
    · intro d hm
      have hd := h.aux_regs d
      simp only [SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false, he.eq_iff] at hm
      exact hd (by simpa using hm)
    · intro d d'; exact he.ne (h.dst_aux d d')
    · exact he.comp h.dst_inj
    · exact he.comp h.aux_inj
    · intro k hk hm
      rcases hk with ⟨f, rfl⟩ | ⟨r, rfl⟩
      · exact h.idx (H.cf f) (Or.inl ⟨f, rfl⟩) (by
          simpa only [SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false, he.eq_iff] using hm)
      · exact h.idx (H.cb off r) (Or.inr ⟨r, rfl⟩) (by
          simpa only [SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false, he.eq_iff] using hm)
    · intro d hk
      rcases hk with ⟨f, hf⟩ | ⟨r, hr⟩
      · exact h.idx_dst d (Or.inl ⟨f, he hf⟩)
      · exact h.idx_dst d (Or.inr ⟨r, he hr⟩)
    · intro d hk
      rcases hk with ⟨f, hf⟩ | ⟨r, hr⟩
      · exact h.idx_aux d (Or.inl ⟨f, he hf⟩)
      · exact h.idx_aux d (Or.inr ⟨r, he hr⟩)
  · intro c; exact he.comp (hH.swap_inj c)
  · intro c j; exact he.ne (hH.swap_src c j)
  · intro c j; exact he.ne (hH.swap_tmp c j)

theorem SetupKey.target_map (key : SetupKey) (H : SelectiveHost T) (e : Fin T → Fin T') :
    key.target (H.map e) = e (key.target H) := by cases key <;> rfl

theorem SelectiveHost.Blank.map_iff (H : SelectiveHost T) (e : Fin T → Fin T')
    (he : Function.Injective e) (k : Fin T) : (H.map e).Blank (e k) ↔ H.Blank k := by
  simp [SelectiveHost.Blank, SelectiveHost.map, he.eq_iff]

theorem SetupLayout.map {H : SelectiveHost T} {cfg : SetupKey → Fin T}
    (layout : SetupLayout H cfg) (e : Fin T → Fin T') (he : Function.Injective e) :
    SetupLayout (H.map e) (fun key => e (cfg key)) where
  targets := by
    intro key other h
    rw [SetupKey.target_map, SetupKey.target_map] at h
    exact layout.targets (he h)
  regs key := by
    rw [SetupKey.target_map]
    simpa only [SelectiveHost.map, List.map_cons, List.map_nil] using (layout.regs key).map he
  sources key other := by
    rw [SetupKey.target_map]
    exact he.ne (layout.sources key other)
  blanks key k hk := by
    rw [SetupKey.target_map]
    intro h
    subst k
    exact layout.blanks key _ ((SelectiveHost.Blank.map_iff H e he _).mp hk) rfl
  stream key := he.ne (layout.stream key)

end IntegerMultBounds.MathlibTM2.Routing
