import GradientHessian.SecondJetAlgebra

/-! Pulling back equality of actual second jets through a smooth physical
coordinate map. This includes the shared continuous linear projections used
by all leaf addresses in the hierarchy. -/

noncomputable section
namespace GradientHessian.SecondJetPullback
open JetLocality SecondJetAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iterated_eq_of_richJet_eq {f g : F → ℝ} {x : F}
    (h : richJet f x = richJet g x) :
    ∀ n ≤ 2, iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x := by
  have h0 : f x=g x := congrArg Prod.fst h
  have h1 : fderiv ℝ f x=fderiv ℝ g x := congrArg (fun t => t.2.1) h
  have h2 : fderiv ℝ (fderiv ℝ f) x=fderiv ℝ (fderiv ℝ g) x := congrArg (fun t => t.2.2) h
  intro n hn
  interval_cases n
  · ext v
    simp only [iteratedFDeriv_zero_apply,h0]
  · ext v
    simp only [iteratedFDeriv_one_apply,h1]
  · ext v
    simp only [iteratedFDeriv_two_apply,h2]

theorem richJet_comp_eq {f g : F → ℝ} {inner : E → F} {x : E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hi : ContDiff ℝ 2 inner)
    (he : richJet f (inner x)=richJet g (inner x)) :
    richJet (f ∘ inner) x=richJet (g ∘ inner) x := by
  apply richJet_eq_of_iterated_eq
  intro n hn
  ext v
  rw [iteratedFDeriv_comp hf.contDiffAt hi.contDiffAt (by exact_mod_cast hn),
    iteratedFDeriv_comp hg.contDiffAt hi.contDiffAt (by exact_mod_cast hn)]
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c _
  rw [iterated_eq_of_richJet_eq he c.length (c.length_le.trans hn)]

theorem richJet_comp_linear_eq {f g : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : richJet f (L x)=richJet g (L x)) :
    richJet (f ∘ L) x=richJet (g ∘ L) x :=
  richJet_comp_eq hf hg L.contDiff he

def ordinary (L : E →L[ℝ] F) (j : ℝ × (F →L[ℝ] ℝ)) : ℝ × (E →L[ℝ] ℝ) :=
  (j.1,j.2.comp L)

theorem ordinaryJet_comp_linear (L : E →L[ℝ] F) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (L x)) :
    ordinaryJet (f ∘ L) x=ordinary L (ordinaryJet f (L x)) :=
  Prod.ext rfl (hf.hasFDerivAt.comp x L.hasFDerivAt).fderiv

theorem ordinary_continuous (L : E →L[ℝ] F) : Continuous (ordinary L) :=
  continuous_fst.prodMk (continuous_snd.clm_comp continuous_const)

end GradientHessian.SecondJetPullback
