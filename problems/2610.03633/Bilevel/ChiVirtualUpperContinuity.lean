import Bilevel.ChiVirtualUpperFormula
import Bilevel.ChiVirtualState

/-! Joint continuity of the complete disclosed-data upper scalar. The macro
chain, release correction, selected carrier, and public bowl are all kept. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem virtualMacroValue_continuous (M : Node E) (ν : ℝ) (rM : ℕ) :
    Continuous (fun p : (Fin (M.n+1) → E) × E => virtualMacroValue M ν rM p.1 p.2) :=
  ((ChiOuter.chain_contDiff M.n M.ell M.width 3).continuous.comp
    (readout_continuous M.n rM M.radius)).add
    ((full_bowl_contDiff (E:=E) ν M.radius 3).continuous.comp continuous_snd)

theorem virtualOuterResidual_continuous (M : Node E) (rM : ℕ) (i : Fin (M.n+1)) :
    Continuous (fun p : (Fin (M.n+1) → E) × E => virtualOuterResidual M rM p.1 i p.2) :=
  continuous_const.mul ((ChiOuter.outer_residual_contDiff M.n i).continuous.comp
    ((readout_continuous M.n rM M.radius).const_smul M.width⁻¹))

theorem virtualOuterReleaseCorrection_continuous (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualOuterReleaseCorrection m M D rM r p.1.1 p.1.2 p.2) := by
  unfold virtualOuterReleaseCorrection
  apply continuous_finset_sum
  intro i _
  have hres := Continuous.comp
    (f:=fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.1,p.2.fst))
    (g:=fun p : (Fin (M.n+1) → E) × E => virtualOuterResidual M rM p.1 i p.2)
    (virtualOuterResidual_continuous M rM i) (macroData_continuous m M D)
  apply hres.mul
  apply Continuous.sub _ continuous_const
  have hcol : Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) => p.1.2 0 [i.val]) :=
    (continuous_apply [i.val]).comp ((continuous_apply 0).comp continuous_fst.snd)
  have hpoint : Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) => block m 0 p.2.snd) :=
    (block (E:=F) m 0).continuous.comp ((innerProjection (E:=E) (F:=F) m).continuous.comp continuous_snd)
  exact Continuous.comp
    (f:=fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.2 0 [i.val],block m 0 p.2.snd))
    (g:=fun p : (Fin ((D 0 [i.val]).n+1) → F) × F => virtualRelease (D 0 [i.val]) (r 0 [i.val]) p.1 p.2)
    (virtualRelease_continuous (D 0 [i.val]) (r 0 [i.val])) (hcol.prodMk hpoint)

theorem virtualUpperBase_continuous (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualUpperBase m M ν D d ρ R rM r p.1.1 p.1.2 p.2) :=
  ((virtualMacroValue_continuous M ν rM).comp (macroData_continuous m M D)).add
    (((virtualOuterReleaseCorrection_continuous m M D rM r).add
      (virtualOuterCarrier_continuous m M D rM r d 0)).add
        ((baseRadial_contDiff m ρ R).continuous.comp continuous_snd))

def stateUpperBase (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (p : VirtualState M D) :
    Joint E (Blocks m F) → ℝ :=
  virtualUpperBase m M ν D d ρ R (rM p.1) (r p.1) p.2.1 p.2.2

theorem stateUpperBase_continuous (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (d : ℕ) (ρ R : ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (fun p : VirtualState M D × Joint E (Blocks m F) =>
      stateUpperBase m M ν D d ρ R rM r p.1 p.2) := by
  have h : Continuous (fun p : ℕ × (HierarchyData M D × Joint E (Blocks m F)) =>
      virtualUpperBase m M ν D d ρ R (rM p.1) (r p.1) p.2.1.1 p.2.1.2 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q =>
      virtualUpperBase_continuous m M ν D d ρ R (rM q) (r q))
  exact Continuous.comp
    (f:=fun p : VirtualState M D × Joint E (Blocks m F) => (p.1.1,(p.1.2,p.2)))
    (g:=fun p : ℕ × (HierarchyData M D × Joint E (Blocks m F)) =>
      virtualUpperBase m M ν D d ρ R (rM p.1) (r p.1) p.2.1.1 p.2.1.2 p.2.2)
    h (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

end Bilevel.ChiPrefixEvaluation



