import Nonsmooth.ParametricSelection

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev ResponseHistory (k n : ℕ) := Fin n → Fin k × ℝ

def responseHistoryJoin {k n : ℕ} (p : ResponseHistory k n × (Fin k × ℝ)) :
    ResponseHistory k (n + 1) := Fin.snoc p.1 p.2

def responseHistorySplit {k n : ℕ} (h : ResponseHistory k (n + 1)) :
    ResponseHistory k n × (Fin k × ℝ) := (Fin.init h, h (Fin.last n))

theorem responseHistoryJoin_measurable {k n : ℕ} :
    Measurable (@responseHistoryJoin k n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [responseHistoryJoin, Fin.snoc_last] using
      (measurable_snd : Measurable (fun p : ResponseHistory k n × (Fin k × ℝ) => p.2))
  · simpa only [responseHistoryJoin, Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_fst : Measurable (fun p : ResponseHistory k n × (Fin k × ℝ) => p.1))

theorem responseHistorySplit_measurable {k n : ℕ} :
    Measurable (@responseHistorySplit k n) := by
  have hi : Measurable (fun h : ResponseHistory k (n + 1) => Fin.init h) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.castSucc
  exact hi.prodMk (measurable_pi_apply (Fin.last n))

theorem responseHistorySplit_join {k n : ℕ} (p : ResponseHistory k n × (Fin k × ℝ)) :
    responseHistorySplit (responseHistoryJoin p) = p := by
  simp only [responseHistorySplit, responseHistoryJoin, Fin.init_snoc, Fin.snoc_last, Prod.mk.eta]

theorem responseHistoryJoin_split {k n : ℕ} (h : ResponseHistory k (n + 1)) :
    responseHistoryJoin (responseHistorySplit h) = h := Fin.snoc_init_self h

def responseHistoryEquiv (k n : ℕ) :
    (ResponseHistory k n × (Fin k × ℝ)) ≃ᵐ ResponseHistory k (n + 1) where
  toFun := responseHistoryJoin
  invFun := responseHistorySplit
  left_inv := responseHistorySplit_join
  right_inv := responseHistoryJoin_split
  measurable_toFun := responseHistoryJoin_measurable
  measurable_invFun := responseHistorySplit_measurable

theorem responseHistoryJoin_fixed_embedding {k n : ℕ} (h : ResponseHistory k n) :
    MeasurableEmbedding (fun y : Fin k × ℝ => responseHistoryJoin (h, y)) := by
  exact (responseHistoryEquiv k n).measurableEmbedding.comp (measurableEmbedding_prodMk_left h)

end
end Nonsmooth
