import MatchingBounds1005.GaussianHaar

/-! # The complete joint law of the chronological Gaussian starts

Flattening the recursive product storage preserves the initial seed times a
literal finite product of independent standard Gaussians. In particular the
starts retain their joint law even though the simulated queries depend on them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open RandomizedFO2003.Rotations
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianHaar

namespace MatchingBounds1005.GaussianStarts
universe u

theorem pairs_joint_preserving (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] :
    MeasurePreserving (fun p : AmbientPairHistory (Vec dim) n H =>
      (AmbientPairHistory.seed (Vec dim) n p, AmbientPairHistory.pairs (Vec dim) n p))
      (gaussianPairLaw dim n μ)
      (μ.prod (Measure.pi (fun _ : Fin n => (standardGaussian dim).prod (standardGaussian dim)))) := by
  induction n generalizing H with
  | zero =>
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [Measure.pi_of_empty _ (Fin.elim0 : Fin 0 → Vec dim × Vec dim), Measure.prod_dirac]
    rfl
  | succ n ih =>
    let σ := standardGaussian dim
    let ν := Measure.pi (fun _ : Fin n => σ.prod σ)
    have ha := (measurePreserving_prodAssoc μ σ σ).prod (MeasurePreserving.id ν)
    have hb := measurePreserving_prodAssoc μ (σ.prod σ) ν
    have hpi := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => σ.prod σ) 0).symm
    have hc := (MeasurePreserving.id μ).prod hpi
    have hh := hc.comp (hb.comp (ha.comp (ih ((μ.prod σ).prod σ))))
    convert hh using 1
    funext p
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [AmbientPairHistory.pairs, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl
      · simp [AmbientPairHistory.pairs, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl

theorem append_preserving {E : Type*} [MeasurableSpace E] (n m : ℕ)
    (σ : Measure E) [IsProbabilityMeasure σ] :
    MeasurePreserving (fun p : (Fin n → E) × (Fin m → E) => Fin.append p.1 p.2)
      ((Measure.pi (fun _ : Fin n => σ)).prod (Measure.pi (fun _ : Fin m => σ)))
      (Measure.pi (fun _ : Fin (n + m) => σ)) := by
  have hm : Measurable (fun p : (Fin n → E) × (Fin m → E) => Fin.append p.1 p.2) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using (measurable_pi_apply j).comp measurable_fst
    · simpa only [Fin.append_right] using (measurable_pi_apply j).comp measurable_snd
  refine ⟨hm, ?_⟩
  apply (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun p : (Fin n → E) × (Fin m → E) => Fin.append p.1 p.2) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun i => s (i.castAdd m))) ×ˢ
        (Set.pi Set.univ (fun i => s (i.natAdd n))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m), fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h, h'⟩ i
      exact Fin.addCases (fun j => by simpa using h j) (fun j => by simpa using h' j) i
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  exact (Fin.prod_univ_add (fun i : Fin (n + m) => σ (s i))).symm

/-- The seed and every original start have their exact joint product law. -/
theorem starts_joint_preserving (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] :
    MeasurePreserving (fun p : AmbientPairHistory (Vec dim) n H =>
      (AmbientPairHistory.seed (Vec dim) n p, AmbientPairHistory.starts (Vec dim) n p))
      (gaussianPairLaw dim n μ)
      (μ.prod (Measure.pi (fun _ : Fin (n + n) => standardGaussian dim))) := by
  have hp := measurePreserving_arrowProdEquivProdArrow (Vec dim) (Vec dim) (Fin n)
    (fun _ => standardGaussian dim) (fun _ => standardGaussian dim)
  have ha := append_preserving n n (standardGaussian dim)
  exact ((MeasurePreserving.id μ).prod (ha.comp hp)).comp (pairs_joint_preserving dim n μ)

/-- The complete family is iid Gaussian, not merely Gaussian in each
individual marginal. -/
theorem starts_preserving (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] :
    MeasurePreserving (AmbientPairHistory.starts (Vec dim) n)
      (gaussianPairLaw dim n μ) (Measure.pi (fun _ : Fin (n + n) => standardGaussian dim)) := by
  have hs : MeasurePreserving (Prod.snd : H × (Fin (n + n) → Vec dim) → (Fin (n + n) → Vec dim))
      (μ.prod (Measure.pi (fun _ : Fin (n + n) => standardGaussian dim)))
      (Measure.pi (fun _ : Fin (n + n) => standardGaussian dim)) := ⟨measurable_snd, by simp⟩
  exact hs.comp (starts_joint_preserving dim n μ)

end MatchingBounds1005.GaussianStarts
