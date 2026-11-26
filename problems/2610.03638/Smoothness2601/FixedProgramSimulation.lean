import Smoothness2601.FixedProgram

/-! Kernel simulation for public program composition. A measurable public
state map is lifted without modifying or inspecting the private oracle state. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.FixedProgram

section KernelSequence
variable {S T : Type} [MeasurableSpace S] [MeasurableSpace T]

def advance (κ : ℕ → Kernel S S) (start : ℕ) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n+1 => κ (start+n) ∘ₖ advance κ start n

theorem advance_add (κ : ℕ → Kernel S S) (start a b : ℕ) :
    advance κ start (a+b) = advance κ (start+a) b ∘ₖ advance κ start a := by
  induction b with
  | zero => simp only [Nat.add_zero, advance, Kernel.id_comp]
  | succ b ih =>
    change κ (start+(a+b)) ∘ₖ advance κ start (a+b) =
      (κ ((start+a)+b) ∘ₖ advance κ (start+a) b) ∘ₖ advance κ start a
    rw [ih, Kernel.comp_assoc, Nat.add_assoc]

theorem advance_simulation (κ : ℕ → Kernel S S) (η : ℕ → Kernel T T)
    (f : S → T) (hf : Measurable f) (a b n : ℕ)
    (hs : ∀ j < n, η (b+j) ∘ₖ Kernel.deterministic f hf =
      Kernel.deterministic f hf ∘ₖ κ (a+j)) :
    advance η b n ∘ₖ Kernel.deterministic f hf =
      Kernel.deterministic f hf ∘ₖ advance κ a n := by
  induction n with
  | zero => simp only [advance, Kernel.id_comp, Kernel.comp_id]
  | succ n ih =>
    have hn := hs n (Nat.lt_succ_self n)
    have hp := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))
    calc
      _ = η (b+n) ∘ₖ (advance η b n ∘ₖ Kernel.deterministic f hf) := Kernel.comp_assoc _ _ _
      _ = η (b+n) ∘ₖ (Kernel.deterministic f hf ∘ₖ advance κ a n) := by rw [hp]
      _ = (η (b+n) ∘ₖ Kernel.deterministic f hf) ∘ₖ advance κ a n := (Kernel.comp_assoc _ _ _).symm
      _ = (Kernel.deterministic f hf ∘ₖ κ (a+n)) ∘ₖ advance κ a n := by rw [hn]
      _ = _ := Kernel.comp_assoc _ _ _

end KernelSequence

def historyMap {S T H : Type} (f : S → T) (z : S × H) : T × H := (f z.1,z.2)
theorem historyMap_measurable {S T H : Type} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace H] {f : S → T} (hf : Measurable f) :
    Measurable (historyMap (H := H) f) := (hf.comp measurable_fst).prodMk measurable_snd

namespace Program
variable {Query Reply A B C D H : Type}
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace H]
  (P : Program Query Reply A B) (Q : Program Query Reply C D)
  (K : Kernel (Query × H) (Reply × H)) [IsMarkovKernel K]

omit [IsMarkovKernel K] in
theorem execution_eq_advance (n : ℕ) : P.execution K n = advance (P.step K) 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [execution, advance, Nat.zero_add, ih]

theorem step_simulation (f : P.State → Q.State) (hf : Measurable f) (k l : ℕ)
    (hq : ∀ s, Q.query l (f s) = P.query k s)
    (hu : ∀ s r, Q.update l (f s,r) = f (P.update k (s,r))) :
    Q.step K l ∘ₖ Kernel.deterministic (historyMap f) (historyMap_measurable hf) =
      Kernel.deterministic (historyMap f) (historyMap_measurable hf) ∘ₖ P.step K k := by
  rw [Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_eq_map]
  ext1 z
  rw [Kernel.comap_apply, Kernel.map_apply _ (historyMap_measurable hf)]
  rw [step, step, KernelMap.dependent_apply _ _ (Q.stepFinish_measurable l),
    KernelMap.dependent_apply _ _ (P.stepFinish_measurable k)]
  simp only [Kernel.comap_apply, stepInput, historyMap, hq]
  have hfinish : Measurable (fun r : Reply × H => P.stepFinish k (z,r)) :=
    (P.stepFinish_measurable k).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map (historyMap_measurable hf) hfinish]
  congr 1
  funext r
  simp only [Function.comp_apply, stepFinish, historyMap, hu]

theorem execution_simulation (f : P.State → Q.State) (hf : Measurable f) (a b n : ℕ)
    (hq : ∀ j < n, ∀ s, Q.query (b+j) (f s) = P.query (a+j) s)
    (hu : ∀ j < n, ∀ s r, Q.update (b+j) (f s,r) = f (P.update (a+j) (s,r))) :
    advance (Q.step K) b n ∘ₖ Kernel.deterministic (historyMap f) (historyMap_measurable hf) =
      Kernel.deterministic (historyMap f) (historyMap_measurable hf) ∘ₖ advance (P.step K) a n :=
  advance_simulation _ _ _ _ a b n
    (fun j hj => step_simulation P Q K f hf (a+j) (b+j) (hq j hj) (hu j hj))

theorem execution_simulation_apply (f : P.State → Q.State) (hf : Measurable f) (a b n : ℕ)
    (hq : ∀ j < n, ∀ s, Q.query (b+j) (f s) = P.query (a+j) s)
    (hu : ∀ j < n, ∀ s r, Q.update (b+j) (f s,r) = f (P.update (a+j) (s,r)))
    (s : P.State) (h : H) :
    advance (Q.step K) b n (f s,h) =
      (advance (P.step K) a n (s,h)).map (historyMap f) := by
  have he := execution_simulation P Q K f hf a b n hq hu
  rw [Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_eq_map] at he
  have hv := congrArg (fun L => L (s,h)) he
  simpa only [Kernel.comap_apply, Kernel.map_apply _ (historyMap_measurable hf), historyMap] using hv

end Program
end Smoothness2601.FixedProgram
