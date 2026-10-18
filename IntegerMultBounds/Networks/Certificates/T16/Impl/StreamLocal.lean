module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Node

/-! The stream semantics of one local template event, explicitly. On a group, the hosted events
of a slot multiply each stream by its accumulated hosted phase; the data events of the active
pair de-frame both streams, shear one into the other and re-frame both at the next level. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open Streams Multiplicative

variable {S : Type*} [AddCommGroup S] [Module ℂ S] (M : Op S)

/-- The accumulated hosted phase of a slot on a stream. -/
def hostAcc (G : GroupData) (slot : ℕ) (i : Fin 8) : Vec :=
  (G.hosted.filter fun h => h.1 = slot ∧ toStream h.2.1 = i).foldr
    (fun h acc => Vec.add (h.2.2, 0) acc) Vec.zero

theorem run_append (p q : List Event) (x : Fin 8 → S) : run M (p ++ q) x = run M q (run M p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih => exact ih _

/-- **Hosted events.** -/
theorem run_hosted (G : GroupData) (slot : ℕ) (x : Fin 8 → S) :
    run M (hostedEvents G slot) x = fun i => M (ofAdd (hostAcc G slot i).toFun) (x i) := by
  unfold hostedEvents hostAcc
  generalize G.hosted = l
  induction l generalizing x with
  | nil =>
    funext i
    simp only [List.filterMap_nil, run, List.filter_nil, List.foldr_nil, Vec.toFun_zero]
    rw [op_zero]
  | cons h l ih =>
    funext i
    by_cases hs : h.1 = slot
    · rw [List.filterMap_cons_some (by split_ifs <;> first | rfl | contradiction)]
      change run M _ (Event.run M (.phase (toStream h.2.1) (h.2.2, 0)) x) i = _
      rw [ih]
      simp only [Event.run]
      by_cases hi : i = toStream h.2.1
      · subst hi
        rw [Function.update_self, List.filter_cons_of_pos (by simp [hs]), List.foldr_cons,
          Vec.toFun_add, add_comm, op_add]
      · rw [Function.update_of_ne hi, List.filter_cons_of_neg (by simp [Ne.symm hi])]
    · rw [List.filterMap_cons_none (by split_ifs <;> first | rfl | contradiction), ih,
        List.filter_cons_of_neg (by simp [hs])]

/-- **Data events.** The forward and reverse sweeps of the active pair. -/
theorem run_data (P : PortData) (stage pair : ℕ) (rev : Bool) (x : Fin 8 → S) (i : Fin 8) :
    run M (dataEvents P stage pair rev) x i =
      if i = toStream (2 * pair) then
        (if rev then M (ofAdd (frameVec P (stage + 1) 0).toFun)
            (M (ofAdd (frameVec P stage 0).neg.toFun) (x i) +
              (-1 : ℤ) • M (ofAdd (frameVec P stage 1).neg.toFun) (x (toStream (2 * pair + 1))))
          else M (ofAdd (frameVec P (stage + 1) 0).toFun)
            (M (ofAdd (frameVec P stage 0).neg.toFun) (x i)))
      else if i = toStream (2 * pair + 1) then
        (if rev then M (ofAdd (frameVec P (stage + 1) 1).toFun)
            (M (ofAdd (frameVec P stage 1).neg.toFun) (x i))
          else M (ofAdd (frameVec P (stage + 1) 1).toFun)
            (M (ofAdd (frameVec P stage 1).neg.toFun) (x i) +
              (1 : ℤ) • M (ofAdd (frameVec P stage 0).neg.toFun) (x (toStream (2 * pair)))))
      else x i := by
  have hxy : toStream (2 * pair) ≠ toStream (2 * pair + 1) := by
    simp only [toStream, ne_eq, Fin.mk.injEq]
    omega
  cases rev <;> by_cases h1 : i = toStream (2 * pair) <;> by_cases h2 : i = toStream (2 * pair + 1) <;>
    simp_all [dataEvents, run, Event.run, Function.update_apply, Ne.symm hxy]

end IntegerMultBounds.Networks.Certificates.T16.Impl
