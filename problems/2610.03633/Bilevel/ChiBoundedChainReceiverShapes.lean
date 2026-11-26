import Bilevel.ChiBoundedChainReceiverProfiles

/-! Exact first and second derivatives of the normalized receiver slopes. -/
noncomputable section
namespace Bilevel.ChiBoundedChain.ReceiverJets

theorem profile_hasDerivAt (i : Fin 3) (t : ℝ) : HasDerivAt (profile i) (deriv (profile i) t) t :=
  ((profile_contDiff i).differentiable (by norm_num) t).hasDerivAt

theorem profile_deriv_hasDerivAt (i : Fin 3) (t : ℝ) :
    HasDerivAt (deriv (profile i)) (iteratedDeriv 2 (profile i) t) t := by
  have hh := ((profile_contDiff i).differentiable_iteratedDeriv 1 (by norm_num) t).hasDerivAt
  simpa only [iteratedDeriv_one,iteratedDeriv_succ] using hh

def positiveShape (a δ t : ℝ) : ℝ := (a*t+1)*profile 0 t*profile 1 (δ*t)
def positiveShapeFirst (a δ t : ℝ) : ℝ :=
  a*profile 0 t*profile 1 (δ*t)+(a*t+1)*deriv (profile 0) t*profile 1 (δ*t)+
    (a*t+1)*profile 0 t*δ*deriv (profile 1) (δ*t)
def positiveShapeSecond (a δ t : ℝ) : ℝ :=
  2*a*deriv (profile 0) t*profile 1 (δ*t)+2*a*profile 0 t*δ*deriv (profile 1) (δ*t)+
    (a*t+1)*iteratedDeriv 2 (profile 0) t*profile 1 (δ*t)+
    2*(a*t+1)*deriv (profile 0) t*δ*deriv (profile 1) (δ*t)+
    (a*t+1)*profile 0 t*δ^2*iteratedDeriv 2 (profile 1) (δ*t)

def negativeShape (δ t : ℝ) : ℝ := profile 0 t*profile 2 (δ*t)
def negativeShapeFirst (δ t : ℝ) : ℝ :=
  deriv (profile 0) t*profile 2 (δ*t)+profile 0 t*δ*deriv (profile 2) (δ*t)
def negativeShapeSecond (δ t : ℝ) : ℝ :=
  iteratedDeriv 2 (profile 0) t*profile 2 (δ*t)+
    2*deriv (profile 0) t*δ*deriv (profile 2) (δ*t)+
    profile 0 t*δ^2*iteratedDeriv 2 (profile 2) (δ*t)

theorem positiveShape_hasDerivAt (a δ t : ℝ) :
    HasDerivAt (positiveShape a δ) (positiveShapeFirst a δ t) t := by
  have ha := ((hasDerivAt_id t).const_mul a).add_const 1
  have hj := profile_hasDerivAt 0 t
  have hk := (profile_hasDerivAt 1 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  convert (ha.mul hj).mul hk using 1
  unfold positiveShapeFirst
  simp only [Function.comp_apply,id_eq]
  ring

theorem positiveShapeFirst_hasDerivAt (a δ t : ℝ) :
    HasDerivAt (positiveShapeFirst a δ) (positiveShapeSecond a δ t) t := by
  have ha := ((hasDerivAt_id t).const_mul a).add_const 1
  have hj := profile_hasDerivAt 0 t
  have hdj := profile_deriv_hasDerivAt 0 t
  have hk := (profile_hasDerivAt 1 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  have hdk := (profile_deriv_hasDerivAt 1 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  have h₁ := (hj.const_mul a).mul hk
  have h₂ := (ha.mul hdj).mul hk
  have h₃ := (((ha.mul hj).mul_const δ).mul hdk)
  convert (h₁.add h₂).add h₃ using 1
  unfold positiveShapeSecond
  simp only [Function.comp_apply,id_eq]
  ring

theorem negativeShape_hasDerivAt (δ t : ℝ) :
    HasDerivAt (negativeShape δ) (negativeShapeFirst δ t) t := by
  have hj := profile_hasDerivAt 0 t
  have hk := (profile_hasDerivAt 2 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  convert hj.mul hk using 1
  unfold negativeShapeFirst
  simp only [Function.comp_apply,id_eq]
  ring

theorem negativeShapeFirst_hasDerivAt (δ t : ℝ) :
    HasDerivAt (negativeShapeFirst δ) (negativeShapeSecond δ t) t := by
  have hj := profile_hasDerivAt 0 t
  have hdj := profile_deriv_hasDerivAt 0 t
  have hk := (profile_hasDerivAt 2 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  have hdk := (profile_deriv_hasDerivAt 2 (δ*t)).comp t ((hasDerivAt_id t).const_mul δ)
  convert (hdj.mul hk).add ((hj.mul_const δ).mul hdk) using 1
  unfold negativeShapeSecond
  simp only [Function.comp_apply,id_eq]
  ring

end Bilevel.ChiBoundedChain.ReceiverJets
