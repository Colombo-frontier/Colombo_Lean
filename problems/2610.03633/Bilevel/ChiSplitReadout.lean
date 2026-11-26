import Bilevel.ChiSplitChainLocality
import Bilevel.ChiSplitChainRegularity
import Bilevel.RadialWrapper

/-! Actual off-graph pullback through two endpoint readouts, including the
full-vector radial wrapper. Gradient membership uses only disclosed endpoint
columns and the queried physical vector. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain PrimitiveGeometry PartialLegendre RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def readout {n : ℕ} (A B : E →L[ℝ] Space n) : E →L[ℝ] Latent n :=
  packLinear.comp (A.prod B)

omit [CompleteSpace E] in
theorem readout_apply {n : ℕ} (A B : E →L[ℝ] Space n) (u : E) : readout A B u=pack (A u) (B u) := rfl

theorem readout_adjoint {n : ℕ} (A B : E →L[ℝ] Space n) (z : Latent n) :
    (readout A B).adjoint z=A.adjoint z.fst+B.adjoint z.snd := by
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,inner_add_left,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,readout_apply]
  rfl

omit [CompleteSpace E] in
theorem readout_norm_le {n : ℕ} (A B : E →L[ℝ] Space n) : ‖readout A B‖≤‖A‖+‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [readout_apply]
  exact (latent_norm_le _ _).trans (by nlinarith only [A.le_opNorm u,B.le_opNorm u])

theorem pullback_gradient {n : ℕ} (A B : E →L[ℝ] Space n) (u : E) :
    gradient (value n ∘ readout A B) u=
      A.adjoint (sourceGradient n (readout A B u))+B.adjoint (targetGradient n (readout A B u)) := by
  have hd := (value_hasGradientAt n (readout A B u)).hasFDerivAt.comp u (readout A B).hasFDerivAt
  have hh : HasGradientAt (value n ∘ readout A B)
      ((readout A B).adjoint (pack (sourceGradient n (readout A B u)) (targetGradient n (readout A B u)))) u := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext w
    simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
  rw [hh.gradient,readout_adjoint]
  rfl

theorem source_force_mem {n : ℕ} (A : E →L[ℝ] Space n) (W : Submodule ℝ E)
    (r : ℕ) (z : Latent n)
    (hknown : ∀ j : Fin (n+1),j.val<r+1 → A.adjoint (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4) :
    A.adjoint (sourceGradient n z)∈W := by
  rw [sourceGradient,map_add,map_smul,map_sum]
  apply W.add_mem (W.smul_mem _ (hknown 0 (by simp)))
  apply W.sum_mem
  intro i _
  rw [map_smul]
  by_cases hi : i.succ.val<r+1
  · exact W.smul_mem _ (hknown i.succ hi)
  · have hb := hz i.castSucc (by
      change ¬ (i.val + 1 < r + 1) at hi
      change r ≤ i.val
      omega)
    rw [edgeRight_inactive _ _ (by linarith only [hb]),zero_smul]
    exact W.zero_mem

theorem target_force_mem {n : ℕ} (B : E →L[ℝ] Space n) (W : Submodule ℝ E)
    (r : ℕ) (z : Latent n)
    (hknown : ∀ j : Fin (n+1),j.val<r → B.adjoint (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4) :
    B.adjoint (targetGradient n z)∈W := by
  rw [targetGradient,map_sum]
  apply W.sum_mem
  intro i _
  rw [map_smul]
  by_cases hi : i.castSucc.val<r
  · exact W.smul_mem _ (hknown i.castSucc hi)
  · have hb := hz i.castSucc (by omega)
    rw [edgeLeft_inactive _ _ (by linarith only [hb]),zero_smul]
    exact W.zero_mem

theorem pullback_gradient_mem {n : ℕ} (A B : E →L[ℝ] Space n) (W : Submodule ℝ E)
    (r : ℕ) (u : E)
    (hsource : ∀ j : Fin (n+1),j.val<r+1 → A.adjoint (basis j)∈W)
    (htarget : ∀ j : Fin (n+1),j.val<r → B.adjoint (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |B u j|≤1/4) :
    gradient (value n ∘ readout A B) u∈W := by
  rw [pullback_gradient]
  exact W.add_mem (source_force_mem A W r (readout A B u) hsource hz)
    (target_force_mem B W r (readout A B u) htarget hz)

theorem wrapped_gradient_mem {n : ℕ} (A B : E →L[ℝ] Space n) (W : Submodule ℝ E)
    (r : ℕ) (ν R : ℝ) (hR : 0<R) (u : E) (hu : u∈W)
    (hsource : ∀ j : Fin (n+1),j.val<r+1 → A.adjoint (basis j)∈W)
    (htarget : ∀ j : Fin (n+1),j.val<r → B.adjoint (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |B (compress R u) j|≤1/4) :
    gradient (wrapped ν R (value n) (readout A B)) u∈W := by
  rw [(wrapped_hasGradientAt ν R hR (value n) (readout A B) u _
    (value_hasGradientAt n (readout A B (compress R u)))).gradient,readout_adjoint]
  apply W.add_mem
  · exact W.smul_mem _ (W.add_mem
      (source_force_mem A W r (readout A B (compress R u)) hsource hz)
      (target_force_mem B W r (readout A B (compress R u)) htarget hz))
  · exact W.smul_mem _ hu

end Bilevel.ChiSplitChain
