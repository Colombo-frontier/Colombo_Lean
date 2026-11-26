import Bilevel.ChiPrefixReadout
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Measurable validity of finite disclosed frame prefixes. Validity uses
only the disclosed Gram entries; the undisclosed numeric tail may be zero.
Countably many node validity conditions may be intersected. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def PrefixGram (n r : ℕ) (columns : Fin (n+1) → E) : Prop :=
  ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0

theorem prefixGram_measurable (n : ℕ) :
    MeasurableSet {p : ℕ × (Fin (n+1) → E) | PrefixGram n p.1 p.2} := by
  have hentry (i j : Fin (n+1)) : MeasurableSet {p : ℕ × (Fin (n+1) → E) |
      ¬i.val<p.1 ∨ ¬j.val<p.1 ∨ ⟪p.2 i,p.2 j⟫=(if i=j then 1 else 0)} := by
    have hi : MeasurableSet {p : ℕ × (Fin (n+1) → E) | i.val<p.1} :=
      measurable_fst (Set.to_countable _).measurableSet
    have hj : MeasurableSet {p : ℕ × (Fin (n+1) → E) | j.val<p.1} :=
      measurable_fst (Set.to_countable _).measurableSet
    have he : Measurable (fun p : ℕ × (Fin (n+1) → E) => ⟪p.2 i,p.2 j⟫) :=
      (continuous_fst.inner continuous_snd).measurable.comp
        (((measurable_pi_apply i).comp measurable_snd).prodMk ((measurable_pi_apply j).comp measurable_snd))
    exact hi.compl.union (hj.compl.union (measurableSet_eq_fun he measurable_const))
  convert MeasurableSet.iInter (fun i => MeasurableSet.iInter (hentry i)) using 1
  ext p
  simp only [PrefixGram,Set.mem_iInter,Set.mem_setOf_eq]
  exact forall_congr' (fun i => forall_congr' (fun j => by tauto))

theorem prefixGram_of_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (r : Ω → ℕ) (hr : Measurable r) (columns : Ω → Fin (n+1) → E) (hc : Measurable columns) :
    MeasurableSet {ω | PrefixGram n (r ω) (columns ω)} :=
  (hr.prodMk hc) (prefixGram_measurable n)

theorem all_prefixGram_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (n : ι → ℕ) (r : ι → Ω → ℕ) (hr : ∀ i,Measurable (r i))
    (columns : ∀ i,Ω → Fin (n i+1) → E) (hc : ∀ i,Measurable (columns i)) :
    MeasurableSet {ω | ∀ i,PrefixGram (n i) (r i ω) (columns i ω)} := by
  simpa only [Set.iInter_setOf] using
    MeasurableSet.iInter (fun i => prefixGram_of_measurable (n i) (r i) (hr i) (columns i) (hc i))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem prefixGram_of_orthonormal (n r : ℕ) (U : Fin (n+1) → E) (hU : Orthonormal ℝ U) :
    PrefixGram n r U := fun i j _ _ => orthonormal_iff_ite.mp hU i j

def paddedPrefix (n r : ℕ) (U : Fin (n+1) → E) : Fin (n+1) → E :=
  fun i => if i.val<r then U i else 0

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem paddedPrefix_measurable (n : ℕ) :
    Measurable (fun p : ℕ × (Fin (n+1) → E) => paddedPrefix n p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  have hi : MeasurableSet {p : ℕ × (Fin (n+1) → E) | i.val<p.1} :=
    measurable_fst (Set.to_countable _).measurableSet
  exact ((measurable_pi_apply i).comp measurable_snd).ite hi measurable_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem paddedPrefix_gram (n r : ℕ) (U : Fin (n+1) → E) (hU : Orthonormal ℝ U) :
    PrefixGram n r (paddedPrefix n r U) := by
  intro i j hi hj
  simpa only [paddedPrefix,if_pos hi,if_pos hj] using orthonormal_iff_ite.mp hU i j

theorem readout_varying_prefix_measurable (n : ℕ) (R : ℝ) :
    Measurable (fun p : ((Fin (n+1) → E) × E) × ℕ => readout n p.2 R p.1.1 p.1.2) :=
  measurable_from_prod_countable (fun r => (readout_continuous (E := E) n r R).measurable)

end Bilevel.ChiPrefixEvaluation
