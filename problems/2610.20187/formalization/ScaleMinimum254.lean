import ClippedMain254
import Mathlib.Topology.Order.Compact

noncomputable section
namespace Paper254

theorem scale_objective_attains_minimum (D : ℝ) (T : ℕ) (hD : 0 < D) (hT : 0 < T)
    (A B : ℝ) :
    ∃ τ ∈ Set.Icc (D/T) D, ∀ σ ∈ Set.Icc (D/T) D,
      A/τ+B*τ^2 ≤ A/σ+B*σ^2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlo : 0 < D/T := div_pos hD hT0
  have hle : D/T ≤ D := (div_le_iff₀ hT0).mpr (by nlinarith)
  have hcont : ContinuousOn (fun τ : ℝ=>A/τ+B*τ^2) (Set.Icc (D/T) D) := by
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun τ hτ=>(hlo.trans_le hτ.1).ne')
    · exact continuousOn_const.mul (continuousOn_id.pow 2)
  exact isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hle) hcont

/-- The for-all-scales certificate really supplies an attained minimum,
as written in the manuscript, rather than only an informal infimum. -/
theorem clipped_main_attained :
    ∃ C : ℝ,0<C ∧
    ∀ D G η : ℝ,0<D → 0<G → 0<η →
    ∀ d T : ℕ,0<d → 0<T → ∀ W : Domain d D,
    ∃ A : OnlineLearner W T,
    ∀ f : Fin T → Loss d,(∀ t,AdmissibleLoss W G η (f t)) →
    ∀ u : Fin T → W.carrier,
    ∃ τ ∈ Set.Icc (D/T) D,
      (∀ σ ∈ Set.Icc (D/T) D,
        Real.sqrt ((d:ℝ)+1)*logFactor T^2/(curvature D G η*τ)*pathLength u+
          curvature D G η*G^2*T*τ^2 ≤
        Real.sqrt ((d:ℝ)+1)*logFactor T^2/(curvature D G η*σ)*pathLength u+
          curvature D G η*G^2*T*σ^2) ∧
      regret A f u ≤ min (G*D*T)
        (C*(((d:ℝ)+1)*logFactor T^2/curvature D G η+
          Real.sqrt ((d:ℝ)+1)*logFactor T^2/(curvature D G η*τ)*pathLength u+
          curvature D G η*G^2*T*τ^2)) := by
  obtain ⟨C,hC,h⟩ := main_clipped_upper
  refine ⟨C,hC,?_⟩
  intro D G η hD hG hη d T hd hT W
  obtain ⟨A,hA⟩ := h D G η hD hG hη d T hd hT W
  refine ⟨A,?_⟩
  intro f hf u
  let B := Real.sqrt ((d:ℝ)+1)*logFactor T^2/curvature D G η*pathLength u
  obtain ⟨τ,hτ,hmin⟩ := scale_objective_attains_minimum D T hD hT B (curvature D G η*G^2*T)
  refine ⟨τ,hτ,?_,?_⟩
  · intro σ hσ
    convert hmin σ hσ using 1 <;> dsimp [B] <;> ring
  · exact le_min (hA f hf u).1 ((hA f hf u).2 τ hτ.1 hτ.2)

end Paper254
#print axioms Paper254.clipped_main_attained
