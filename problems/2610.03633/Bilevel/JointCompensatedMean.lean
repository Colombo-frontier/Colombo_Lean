import Bilevel.CompensatedMeanHessian
import Bilevel.PrimitiveGeometry

/-! Exact additive compensated mean with an independent macro variable.

The residual and every multiscale component depend jointly on `(x,u)`.
The lower variable is exactly `(u,s)`, with no auxiliary quadratic coordinate.
The quantitative Hessian and normal-core hypotheses below are explicit;
instantiating the manuscript's selected hierarchy is a separate obligation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped RealInnerProductSpace
namespace Bilevel.JointCompensatedMean
open PrimitiveGeometry

variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

abbrev Data := CompensatedMean.Data (E := Joint X U)

def embed (x : X) (y : Joint U ℝ) : CompensatedMean.LowerSpace (Joint X U) :=
  CompensatedMean.pack _ (pack x y.fst) y.snd 0

def perturbation (P : Data (X:=X) (U:=U)) (x : X) (y : Joint U ℝ) : ℝ :=
  P.μ/(2*P.L^2)*(P.r (pack x y.fst))^2 -
    P.μ/P.L*∑ j ∈ Finset.range (P.J+1),
      P.e j (pack x y.fst)*SmallGapProfiles.normal (P.w j) y.snd

def upper (P : Data (X:=X) (U:=U)) (x : X) (_v : U) (y : Joint U ℝ) : ℝ :=
  P.A (pack x y.fst)+P.L*y.snd

def lower (P : Data (X:=X) (U:=U)) (x : X) (v : U) (y : Joint U ℝ) : ℝ :=
  P.μ/2*(‖y.fst‖^2+y.snd^2)-P.L*⟪v,y.fst⟫+perturbation P x y

def response (P : Data (X:=X) (U:=U)) (x : X) (v : U) : Joint U ℝ :=
  pack ((P.L/P.μ) • v) (P.r (pack x ((P.L/P.μ) • v))/P.L)

omit [CompleteSpace X] [CompleteSpace U] in
theorem perturbation_eq_embed (P : Data (X:=X) (U:=U)) (x : X) (y : Joint U ℝ) :
    perturbation P x y=P.perturbation (embed x y) := by
  simp only [perturbation, CompensatedMean.Data.perturbation, embed,
    CompensatedMean.uProj_pack, CompensatedMean.sProj_pack]

omit [CompleteSpace X] [CompleteSpace U] in
theorem lower_eq_restriction (P : Data (X:=X) (U:=U)) (hL : P.L≠0)
    (x : X) (v : U) (y : Joint U ℝ) :
    lower P x v y =
      P.lower (pack ((P.μ/P.L) • x) v) (embed x y)+P.μ/2*‖x‖^2 := by
  rw [lower, perturbation_eq_embed]
  simp only [CompensatedMean.Data.lower, embed, CompensatedMean.uProj_pack,
    CompensatedMean.sProj_pack, CompensatedMean.zProj_pack, zero_pow (by omega : 2≠0),
    mul_zero, add_zero, WithLp.prod_inner_apply]
  change P.μ/2*(‖y.fst‖^2+y.snd^2)-P.L*⟪v,y.fst⟫+
    P.perturbation (CompensatedMean.pack _ (pack x y.fst) y.snd 0) =
    P.μ/2*(‖pack x y.fst‖^2+y.snd^2)-
      P.L*(⟪(P.μ/P.L) • x,x⟫+⟪v,y.fst⟫)+
      P.perturbation (CompensatedMean.pack _ (pack x y.fst) y.snd 0)+P.μ/2*‖x‖^2
  rw [real_inner_smul_left,real_inner_self_eq_norm_sq,norm_sq]
  change _ = P.μ/2*(‖x‖^2+‖y.fst‖^2+y.snd^2)-
      P.L*(P.μ/P.L*‖x‖^2+⟪v,y.fst⟫)+
      P.perturbation (CompensatedMean.pack _ (pack x y.fst) y.snd 0)+P.μ/2*‖x‖^2
  field_simp
  ring

omit [CompleteSpace X] [CompleteSpace U] in
theorem embed_response (P : Data (X:=X) (U:=U)) (hμ : P.μ≠0) (hL : P.L≠0)
    (x : X) (v : U) :
    embed x (response P x v)=P.response (pack ((P.μ/P.L) • x) v) := by
  have hu : (P.L/P.μ) • pack ((P.μ/P.L) • x) v = pack x ((P.L/P.μ) • v) := by
    apply (WithLp.equiv 2 (X×U)).injective
    apply Prod.ext
    · change (P.L/P.μ) • ((P.μ/P.L) • x)=x
      rw [smul_smul]
      have he : P.L/P.μ*(P.μ/P.L)=1 := by field_simp
      rw [he,one_smul]
    · rfl
  simp only [embed,response,CompensatedMean.Data.response,hu]
  rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem embed_injective (x : X) : Function.Injective (embed (U:=U) x) := by
  intro y z h
  have hu := congrArg (fun w => (CompensatedMean.uProj (Joint X U) w).snd) h
  have hs := congrArg (CompensatedMean.sProj (Joint X U)) h
  apply (WithLp.equiv 2 (U×ℝ)).injective
  exact Prod.ext hu (by simpa only [embed,CompensatedMean.sProj_pack] using hs)

theorem response_minimizes (P : Data (X:=X) (U:=U))
    (hμ : 0<P.μ) (hμL : P.μ≤P.L)
    (hpert : ∀ y, ‖iteratedFDeriv ℝ 2 P.perturbation y‖≤P.μ/2)
    (hcore : ∀ z j, j≤P.J → |P.r z/P.L|≤P.w j/4)
    (x : X) (v : U) (y : Joint U ℝ) :
    lower P x v (response P x v)≤lower P x v y := by
  have hL : P.L≠0 := ne_of_gt (hμ.trans_le hμL)
  rw [lower_eq_restriction P hL,lower_eq_restriction P hL,
    embed_response P hμ.ne' hL]
  exact add_le_add_right (P.response_minimizes hμ hμL hL hpert hcore _ _) _

theorem response_unique (P : Data (X:=X) (U:=U))
    (hμ : 0<P.μ) (hμL : P.μ≤P.L)
    (hpert : ∀ y, ‖iteratedFDeriv ℝ 2 P.perturbation y‖≤P.μ/2)
    (hcore : ∀ z j, j≤P.J → |P.r z/P.L|≤P.w j/4)
    (x : X) (v : U) (y : Joint U ℝ)
    (hy : lower P x v y≤lower P x v (response P x v)) :
    y=response P x v := by
  have hL : P.L≠0 := ne_of_gt (hμ.trans_le hμL)
  rw [lower_eq_restriction P hL,lower_eq_restriction P hL,
    embed_response P hμ.ne' hL] at hy
  apply embed_injective x
  rw [embed_response P hμ.ne' hL]
  exact P.response_unique hμ hμL hL hpert hcore _ _ ((add_le_add_iff_right _).mp hy)

omit [CompleteSpace X] [CompleteSpace U] in
theorem hyperobjective_substitution (P : Data (X:=X) (U:=U)) (hL : P.L≠0)
    (x : X) (v : U) :
    upper P x v (response P x v)=
      P.A (pack x ((P.L/P.μ) • v))+P.r (pack x ((P.L/P.μ) • v)) := by
  change _+P.L*(_/P.L)=_+_
  rw [mul_div_cancel₀ _ hL]
  rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem response_zero (P : Data (X:=X) (U:=U)) (hr : P.r 0=0) :
    response P (0:X) (0:U)=0 := by
  simp only [response,smul_zero]
  have hpack : pack (0:X) (0:U)=0 := rfl
  rw [hpack,hr,zero_div]
  rfl

end Bilevel.JointCompensatedMean
