import Bilevel.BorelAdaptiveFreshness
import Bilevel.IndependentStream

/-! Fresh-draw independence on the ordinary product prior used for the
hard-instance/seed decomposition, with an actual countable iid draw stream. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.BorelAdaptive

variable {C : Type*} [MeasurableSpace C]

def drawPrefix (n : ℕ) (x : ℕ → C) : Fin n → C := fun i => x i

theorem drawPrefix_measurable (n : ℕ) : Measurable (drawPrefix (C:=C) n) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

theorem drawPrefix_fresh_independent (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (drawPrefix n) (fun x : ℕ → C => x n) (IndependentStream.law ν) := by
  have hd : Disjoint (Finset.range n) {n} := Finset.disjoint_singleton_right.mpr (by simp)
  have hi := (IndependentStream.coordinates_independent ν).indepFun_finset
    (Finset.range n) {n} hd (fun i => measurable_pi_apply i)
  exact hi.comp (measurable_pi_lambda _ (fun i : Fin n =>
    measurable_pi_apply (⟨i.val,Finset.mem_range.mpr i.isLt⟩ : Finset.range n)))
    (measurable_pi_apply (⟨n,by simp⟩ : ({n} : Finset ℕ)))

def prefixLaw (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) : Measure (Fin n → C) :=
  (IndependentStream.law ν).map (drawPrefix n)

instance prefixLaw_probability (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (prefixLaw ν n) :=
  isProbabilityMeasure_map (drawPrefix_measurable n).aemeasurable

theorem prefix_fresh_preserving (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun x : ℕ → C => (drawPrefix n x,x n))
      (IndependentStream.law ν) ((prefixLaw ν n).prod ν) := by
  refine ⟨(drawPrefix_measurable n).prodMk (measurable_pi_apply n),?_⟩
  have h := (indepFun_iff_map_prod_eq_prod_map_map (drawPrefix_measurable n).aemeasurable
    (measurable_pi_apply n).aemeasurable).mp (drawPrefix_fresh_independent ν n)
  simpa only [(IndependentStream.coordinate_preserves ν n).map_eq,prefixLaw] using h

theorem initial_prefix_fresh_preserving {Seed : Type*} [MeasurableSpace Seed]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun p : Seed × (ℕ → C) => ((p.1,drawPrefix n p.2),p.2 n))
      (ρ.prod (IndependentStream.law ν)) ((ρ.prod (prefixLaw ν n)).prod ν) := by
  have ha := (measurePreserving_prodAssoc ρ (prefixLaw ν n) ν).symm
    (MeasurableEquiv.prodAssoc : (Seed × (Fin n → C)) × C ≃ᵐ Seed × ((Fin n → C) × C))
  exact ha.comp ((MeasurePreserving.id ρ).prod (prefix_fresh_preserving ν n))

theorem independent_of_pair_preserving {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {νA : Measure A} [IsProbabilityMeasure νA]
    {νB : Measure B} [IsProbabilityMeasure νB] {f : Ω → A} {g : Ω → B}
    (h : MeasurePreserving (fun x => (f x,g x)) μ (νA.prod νB)) : IndepFun f g μ := by
  have hf : MeasurePreserving Prod.fst (νA.prod νB) νA :=
    ⟨measurable_fst,by simp only [Measure.map_fst_prod,measure_univ,one_smul]⟩
  have hg : MeasurePreserving Prod.snd (νA.prod νB) νB :=
    ⟨measurable_snd,by simp only [Measure.map_snd_prod,measure_univ,one_smul]⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map (hf.comp h).measurable.aemeasurable
    (hg.comp h).measurable.aemeasurable).mpr
  change μ.map (fun x => (f x,g x)) = (μ.map f).prod (μ.map g)
  rw [h.map_eq,show μ.map f = νA from (hf.comp h).map_eq,
    show μ.map g = νB from (hg.comp h).map_eq]

variable {S Q O Y I Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace Private]

def seededState (A : Program S Q O Y) (response : I → Q → C → O)
    (initial : Private → S) (n : ℕ) (p : Sample I Private C) : S :=
  run A response p.1 p.2.2 (initial p.2.1) n

theorem seeded_prefix_fresh_preserving
    (νI : Measure I) [IsProbabilityMeasure νI] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun p : Sample I Private C => (((p.1,p.2.1),drawPrefix n p.2.2),p.2.2 n))
      (νI.prod (ρ.prod (IndependentStream.law ν)))
      (((νI.prod ρ).prod (prefixLaw ν n)).prod ν) := by
  have ha := (measurePreserving_prodAssoc νI ρ (IndependentStream.law ν)).symm
    (MeasurableEquiv.prodAssoc : (I × Private) × (ℕ → C) ≃ᵐ Sample I Private C)
  exact (initial_prefix_fresh_preserving (νI.prod ρ) ν n).comp ha

theorem seededState_fresh_independent [Inhabited C] (A : Program S Q O Y)
    (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (νI : Measure I) [IsProbabilityMeasure νI] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (seededState A response initial n) (fun p : Sample I Private C => p.2.2 n)
      (νI.prod (ρ.prod (IndependentStream.law ν))) := by
  let state : (I × Private) × (Fin n → C) → S :=
    fun p => finiteRun A response n (p.1.1,(initial p.1.2,p.2))
  have hm : Measurable state := (finiteRun_measurable A response hr n).comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((hi.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  have h := (independent_of_pair_preserving (seeded_prefix_fresh_preserving νI ρ ν n)).comp hm measurable_id
  have he : (fun p : Sample I Private C => state ((p.1,p.2.1),drawPrefix n p.2.2)) =
      seededState A response initial n := by
    funext p
    exact (run_eq_finiteRun A response p.1 p.2.2 (initial p.2.1) n).symm
  simpa only [Function.comp_def,he] using h

theorem seededQuery_fresh_independent [Inhabited C] (A : Program S Q O Y)
    (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (νI : Measure I) [IsProbabilityMeasure νI] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (ν : Measure C) [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (fun p => A.query (seededState A response initial n p))
      (fun p : Sample I Private C => p.2.2 n) (νI.prod (ρ.prod (IndependentStream.law ν))) :=
  (seededState_fresh_independent A response hr initial hi νI ρ ν n).comp A.query_measurable measurable_id

end Bilevel.BorelAdaptive
