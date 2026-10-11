module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant

/-! Saved caller frames are protected tape prefixes, rather than a claimed
equality of whole dormant banks. Nested saves may write above their boundary;
nested restores may erase above it. Local scalar and basis endpoints retain
the designated stack cells. Recursive induction must retain these propositions
through every child event before the final caller frame is consumed. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {s : ℕ}

def protectedSlots (headerStack liveStack pcStack : Fin s) (i : Fin (10+s)) : Prop :=
  i=Fin.natAdd 10 headerStack ∨ i=Fin.natAdd 10 liveStack ∨
    i=Fin.natAdd 10 pcStack ∨ i=⟨9,by omega⟩

theorem protected_ne_live (headerStack liveStack pcStack : Fin s)
    (i : Fin (10+s)) (hi : protectedSlots headerStack liveStack pcStack i) :
    i≠⟨7,by omega⟩ := by
  rcases hi with rfl|rfl|rfl|rfl <;>
    intro he <;> have hv := congrArg Fin.val he <;> simp only [Fin.val_natAdd] at hv <;> omega

/-- Capture references the literal bank after this caller's frame was saved.
Only the cells below those actual head positions are frozen. -/
structure Snapshot (s : ℕ) where
  headerStack : Fin s
  liveStack : Fin s
  pcStack : Fin s
  storage : Tapes (10+s) 2
  aux : Tapes 2 2

def Holds (snapshot : Snapshot s) (storage : Tapes (10+s) 2) (aux : Tapes 2 2) : Prop :=
  (∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
    snapshot.storage.head i≤storage.head i ∧
      ∀ z,z<snapshot.storage.head i → storage.tape i z=snapshot.storage.tape i z) ∧
  snapshot.aux.head 0≤aux.head 0 ∧
    ∀ z,z<snapshot.aux.head 0 → aux.tape 0 z=snapshot.aux.tape 0 z

theorem captured (snapshot : Snapshot s) : Holds snapshot snapshot.storage snapshot.aux :=
  ⟨fun _ _ => ⟨le_rfl,fun _ _ => rfl⟩,le_rfl,fun _ _ => rfl⟩

/-- At a completed recursive boundary the saved stacks have their original
heads again. Their clean upper tails, together with the protected prefixes,
recover exact individual dormant tape words. These are completion-invariant
obligations, not an execution theorem. -/
structure Settled (snapshot : Snapshot s) (storage : Tapes (10+s) 2) (aux : Tapes 2 2) : Prop where
  preserved : Holds snapshot storage aux
  storage_heads : ∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
    storage.head i=snapshot.storage.head i
  storage_clean : ∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
    ∀ z,snapshot.storage.head i≤z → storage.tape i z=blank
  reference_clean : ∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
    ∀ z,snapshot.storage.head i≤z → snapshot.storage.tape i z=blank
  aux_head : aux.head 0=snapshot.aux.head 0
  aux_clean : ∀ z,snapshot.aux.head 0≤z → aux.tape 0 z=blank
  aux_reference_clean : ∀ z,snapshot.aux.head 0≤z → snapshot.aux.tape 0 z=blank

theorem settled_storage {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) (i : Fin (10+s))
    (hi : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i) :
    storage.head i=snapshot.storage.head i ∧ storage.tape i=snapshot.storage.tape i := by
  refine ⟨h.storage_heads i hi,?_⟩
  funext z
  by_cases hz : z<snapshot.storage.head i
  · exact (h.preserved.1 i hi).2 z hz
  · rw [h.storage_clean i hi z (by omega),h.reference_clean i hi z (by omega)]

theorem settled_aux {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) :
    aux.head 0=snapshot.aux.head 0 ∧ aux.tape 0=snapshot.aux.tape 0 := by
  refine ⟨h.aux_head,?_⟩
  funext z
  by_cases hz : z<snapshot.aux.head 0
  · exact h.preserved.2.2 z hz
  · rw [h.aux_clean z (by omega),h.aux_reference_clean z (by omega)]

/-- Descriptor pushes retain a clean tail at their genuine new stack head. -/
theorem descriptor_push_clean (f : ℤ → Fin 6) (p : ℤ) (xs : List Bool)
    (hf : ∀ z,p≤z → f z=blank) :
    ∀ z,p+1+xs.length≤z → BinaryDescriptorStack.frame f p xs z=blank := by
  intro z hz
  rw [BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inr hz)]
  exact hf z (by omega)

/-- Erasure of the popped descriptor region and a clean incoming tail derive
the restored tape's clean tail at its actual old head. -/
theorem descriptor_pop_clean (f : ℤ → Fin 6) (p : ℤ) (xs : List Bool)
    (hregion : ∀ z,p≤z → z<p+1+xs.length → f z=blank)
    (htail : ∀ z,p+1+xs.length≤z → BinaryDescriptorStack.frame f p xs z=blank) :
    ∀ z,p≤z → f z=blank := by
  intro z hz
  by_cases ht : z<p+1+xs.length
  · exact hregion z hz ht
  · have hb := htail z (by omega)
    rwa [BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inr (by omega))] at hb

/-- The real payload parking word is clean beyond the counted saved region. -/
theorem payload_push_clean (f role : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (hf : ∀ z,p≤z → f z=blank) :
    ∀ z,p+n≤z → RoleArrayStack.parked f role p n z=blank := by
  intro z hz
  simpa only [RoleArrayStack.parked,show ¬(p≤z ∧ z<p+n) by omega,ite_false] using hf z (by omega)

/-- Payload recovery's erasure range and retained upper tail imply clean
stack space above the genuine recovered parent head. -/
theorem payload_pop_clean (f role : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (hregion : ∀ z,p≤z → z<p+n → f z=blank)
    (htail : ∀ z,p+n≤z → RoleArrayStack.parked f role p n z=blank) :
    ∀ z,p≤z → f z=blank := by
  intro z hz
  by_cases ht : z<p+n
  · exact hregion z hz ht
  · have hb := htail z (by omega)
    simpa only [RoleArrayStack.parked,show ¬(p≤z ∧ z<p+n) by omega,ite_false] using hb

/-- A genuinely unprotected storage update retains every saved frame. -/
theorem storage_update {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s))
    (hi : ¬protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i)
    (f : ℤ → Fin 6) (p : ℤ) : Holds snapshot (setTape storage i f p) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  have hne : j≠i := by intro he;subst j;exact hi hj
  simpa only [setTape,Function.update_of_ne hne] using h.1 j hj

/-- The literal scalar endpoint changes storage7 alone. -/
theorem scalar_storage {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (n : ℕ) :
    Holds snapshot (CompactComplexScalarCallerEndpoint.storageOutput (by omega) storage n) aux := by
  apply storage_update h
  intro hi
  exact protected_ne_live _ _ _ _ hi rfl

/-- A nested descriptor push preserves the older caller's exact saved words.
The pushed endpoint is the real BinaryDescriptorStack frame. -/
theorem descriptor_push {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s)) (xs : List Bool) :
    Holds snapshot (setTape storage i (BinaryDescriptorStack.frame (storage.tape i) (storage.head i) xs)
      (storage.head i+1+xs.length)) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  by_cases hji : j=i
  · subst j
    have hold := h.1 i hj
    refine ⟨by simpa only [setTape,Function.update_self] using
      (show snapshot.storage.head i≤storage.head i+1+xs.length by omega),?_⟩
    intro z hz
    simp only [setTape,Function.update_self]
    rw [BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inl (by omega))]
    exact hold.2 z hz
  · simpa only [setTape,Function.update_of_ne hji] using h.1 j hj

/-- A nested descriptor pop erases only its own frame above the older saved
boundary. Its actual decoded old word supplies the restored endpoint. -/
theorem descriptor_pop {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s)) (f : ℤ → Fin 6) (p : ℤ) (xs : List Bool)
    (ht : storage.tape i=BinaryDescriptorStack.frame f p xs)
    (hp : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i → snapshot.storage.head i≤p) :
    Holds snapshot (setTape storage i f p) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  by_cases hji : j=i
  · subst j
    refine ⟨by simpa only [setTape,Function.update_self] using hp hj,?_⟩
    intro z hz
    simp only [setTape,Function.update_self]
    have hold := (h.1 i hj).2 z hz
    rw [ht,BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inl (by have := hp hj;omega))] at hold
    exact hold
  · simpa only [setTape,Function.update_of_ne hji] using h.1 j hj

/-- All three original geometric descriptors are saved above the same
dormant boundary. Their actual chronological frame word is retained. -/
theorem headers_push {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s)) (data : Fin 3 → List Bool) :
    Holds snapshot (setTape storage i
      (CompactChildHeadersStack.frames (storage.tape i) (storage.head i) data)
      (CompactChildHeadersStack.top (storage.head i) data)) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  by_cases hji : j=i
  · subst j
    have hold := h.1 i hj
    refine ⟨?_,?_⟩
    · simp only [setTape,Function.update_self,CompactChildHeadersStack.top,CompactChildHeadersStack.next]
      omega
    · intro z hz
      simp only [setTape,Function.update_self,CompactChildHeadersStack.frames]
      rw [BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inl (by
        unfold CompactChildHeadersStack.next;omega)),
        BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inl (by
          unfold CompactChildHeadersStack.next;omega)),
        BinaryDescriptorStack.frame_outside _ _ _ _ (Or.inl (by omega))]
      exact hold.2 z hz
  · simpa only [setTape,Function.update_of_ne hji] using h.1 j hj

/-- The original finite return-PC word is saved strictly above the dormant
caller boundary, just like the descriptor and payload stacks. -/
theorem pc_push {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s)) {k : ℕ} (code : FiniteReturnStack.Code k) :
    Holds snapshot (setTape storage i
      (FiniteReturnStack.wordPart (storage.tape i) (storage.head i) code k le_rfl)
      (storage.head i+k)) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  by_cases hji : j=i
  · subst j
    have hold := h.1 i hj
    refine ⟨by simpa only [setTape,Function.update_self] using
      (show snapshot.storage.head i≤storage.head i+k by omega),?_⟩
    intro z hz
    simp only [setTape,Function.update_self,FiniteReturnStack.wordPart,
      show ¬(storage.head i≤z ∧ z<storage.head i+k) by omega]
    exact hold.2 z hz
  · simpa only [setTape,Function.update_of_ne hji] using h.1 j hj

/-- The decoded PC pop restores the older word without touching a dormant
caller below its true pop base. -/
theorem pc_pop {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (i : Fin (10+s)) (f : ℤ → Fin 6) (p : ℤ)
    {k : ℕ} (code : FiniteReturnStack.Code k)
    (ht : storage.tape i=FiniteReturnStack.wordPart f p code k le_rfl)
    (hp : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i → snapshot.storage.head i≤p) :
    Holds snapshot (setTape storage i f p) aux := by
  refine ⟨?_,h.2⟩
  intro j hj
  by_cases hji : j=i
  · subst j
    refine ⟨by simpa only [setTape,Function.update_self] using hp hj,?_⟩
    intro z hz
    simp only [setTape,Function.update_self]
    have hold := (h.1 i hj).2 z hz
    rw [ht] at hold
    simpa only [FiniteReturnStack.wordPart,
      show ¬(p≤z ∧ z<p+k) by have := hp hj;omega,dite_false] using hold
  · simpa only [setTape,Function.update_of_ne hji] using h.1 j hj

/-- Actual descriptor save, with its exact runtime and the dormant invariant
on the literal physical output. No execution hypothesis is supplied. -/
theorem descriptor_push_runs {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (src stack : Fin (10+s)) (hne : src≠stack)
    (xs : List Bool) (ht : storage.tape src=BinaryDescriptorStack.descriptor xs)
    (hh : storage.head src=1) :
    HoareTime (BinaryDescriptorStackAt.pushProgram src stack hne) (fun w => w=storage)
      (fun w => w=setTape storage stack
        (BinaryDescriptorStack.frame (storage.tape stack) (storage.head stack) xs)
        (storage.head stack+1+xs.length)) (2*xs.length+7) ∧
    Holds snapshot (setTape storage stack
      (BinaryDescriptorStack.frame (storage.tape stack) (storage.head stack) xs)
      (storage.head stack+1+xs.length)) aux :=
  ⟨BinaryDescriptorStackAt.push_hoare src stack hne storage xs ht hh,descriptor_push h stack xs⟩

/-- Actual descriptor restore pays its runtime and preserves the older
caller's frame while writing its numeric result to an unprotected slot. -/
theorem descriptor_pop_runs {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (stack dst : Fin (10+s)) (hne : stack≠dst)
    (f : ℤ → Fin 6) (p : ℤ) (xs : List Bool)
    (ht : storage.tape stack=BinaryDescriptorStack.frame f p xs)
    (hh : storage.head stack=p+1+xs.length) (hd : storage.tape dst=(fun _ => blank))
    (hdh : storage.head dst=0) (hf : ∀ z,p≤z → z<p+1+xs.length → f z=blank)
    (hp : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack stack → snapshot.storage.head stack≤p)
    (hdst : ¬protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack dst) :
    HoareTime (BinaryDescriptorStackAt.popProgram stack dst hne) (fun w => w=storage)
      (fun w => w=setTape (setTape storage stack f p) dst (BinaryDescriptorStack.descriptor xs) 1)
      (2*xs.length+7) ∧
    Holds snapshot (setTape (setTape storage stack f p) dst (BinaryDescriptorStack.descriptor xs) 1) aux :=
  ⟨BinaryDescriptorStackAt.pop_hoare stack dst hne storage f p xs ht hh hd hdh hf,
    storage_update (descriptor_pop h stack f p xs ht hp) dst hdst _ 1⟩

/-- Literal payload parking writes above the actual current stack head. -/
theorem payload_push {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (role : ℤ → Fin 6) (n : ℕ) :
    Holds snapshot storage (setTape aux 0 (RoleArrayStack.parked (aux.tape 0) role (aux.head 0) n)
      (aux.head 0+n)) := by
  refine ⟨h.1,?_,?_⟩
  · simpa only [setTape,Function.update_self] using
      (show snapshot.aux.head 0≤aux.head 0+n by have := h.2.1;omega)
  · intro z hz
    simp only [setTape,Function.update_self,RoleArrayStack.parked,
      show ¬(aux.head 0≤z ∧ z<aux.head 0+n) by have := h.2.1;omega,ite_false]
    exact h.2.2 z hz

/-- The actual restored payload word retains older frames below its pop base. -/
theorem payload_pop {snapshot : Snapshot s} {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Holds snapshot storage aux) (f role : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (ht : aux.tape 0=RoleArrayStack.parked f role p n) (hp : snapshot.aux.head 0≤p) :
    Holds snapshot storage (setTape aux 0 f p) := by
  refine ⟨h.1,by simpa only [setTape,Function.update_self] using hp,?_⟩
  intro z hz
  simp only [setTape,Function.update_self]
  have hold := h.2.2 z hz
  rw [ht] at hold
  simpa only [RoleArrayStack.parked,
    show ¬(p≤z ∧ z<p+n) by omega,ite_false] using hold

section Permanent
variable {c : ℕ}
open CompactComplexNativeCodecFrame (bank permanentTapes)

def storageOf (w : Tapes (permanentTapes (10+s) c) 2) : Tapes (10+s) 2 :=
  ⟨fun i => w.head (CompactComplexSpectatorTargetBank.oldSlot i),
    fun i => w.tape (CompactComplexSpectatorTargetBank.oldSlot i)⟩

theorem storageOf_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) :
    storageOf (bank control queue scalar stage tail storage payload)=storage := by
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload i).1
  · exact (CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload i).2

def BankHolds (snapshot : Snapshot s) (w : Tapes (permanentTapes (10+s) c) 2) (aux : Tapes 2 2) :=
  Holds snapshot (storageOf w) aux

/-- Actual scalar caller endpoints retain the dormant storage and payload
stack frames, independently of the arrays emitted on the live role ports. -/
theorem scalar_bank {snapshot : Snapshot s} (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2)
    (h : BankHolds snapshot (bank control queue scalar stage tail storage payload) aux)
    (n : ℕ) (words : Fin c → ℤ → Fin 6) :
    BankHolds snapshot (bank control queue scalar stage tail
      (CompactComplexScalarCallerEndpoint.storageOutput (by omega) storage n)
      (CompactComplexScalarCallerEndpoint.emitted payload words)) aux := by
  unfold BankHolds at h ⊢
  rw [storageOf_bank] at h ⊢
  exact scalar_storage h n

/-- The real basis endpoint updates its selected role port and retains every
physical saved storage cell and the complete payload-stack auxiliary tapes. -/
theorem basis_bank {snapshot : Snapshot s} (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2)
    (h : BankHolds snapshot (bank control queue scalar stage tail storage payload) aux)
    (j : Fin c) (word : ℤ → Fin 6) (head : ℤ) :
    BankHolds snapshot (setTape (bank control queue scalar stage tail storage payload)
      (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) j) word head) aux := by
  rw [←CompactComplexSourceReadyReachedBasisInvariant.bank_role_replace]
  unfold BankHolds at h ⊢
  rw [storageOf_bank] at h ⊢
  exact h

end Permanent

/-- The actual decoded-return frame projection reads precisely the supplied
nine-tape physical frame. In particular an auxiliary pair plus empty7 retains
literal private-work blankness at this boundary. -/
theorem frame_entry {c : ℕ}
    (w : Tapes (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) 2) (fr : Tapes 9 2) :
    CompactComplexSourceReadyChildReturnPath.frame
      (CompactComplexNonleafSpectatorTargetRestore.entry w fr)=fr := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (w.append fr).head ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c)
      ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) i)))=fr.head i
    rw [Equiv.apply_symm_apply]
    simp only [Tapes.append,Fin.addCases_right]
  · funext i
    change (w.append fr).tape ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c)
      ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) i)))=fr.tape i
    rw [Equiv.apply_symm_apply]
    simp only [Tapes.append,Fin.addCases_right]


end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant
