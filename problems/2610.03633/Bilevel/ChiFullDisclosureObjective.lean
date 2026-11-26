import Bilevel.ChiFullDisclosure

/-! A continuous disclosed-array formula for the complete mean objective,
with every recursive payload and public radial term retained. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem virtualMacroValue_full (M : Node E) (ν : ℝ) (u : E) :
    virtualMacroValue M ν (M.n+1) (nodeColumns M) u=
      macroValue M.n M.ell M.width ν M.radius M.frame u := by
  unfold virtualMacroValue macroValue
  rw [readout_full]
  rfl

theorem virtualOuterResidual_full (M : Node E) (i : Fin (M.n+1)) (u : E) :
    virtualOuterResidual M (M.n+1) (nodeColumns M) i u=wrappedResidual M i u := by
  unfold virtualOuterResidual wrappedResidual
  rw [readout_full]

def virtualJointOuter (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ColumnData D) (z : Joint E (Blocks m F)) : ℝ :=
  let u := padded (K • z.snd)
  (virtualMacroValue M ν rM macroColumns z.fst+
    ∑ i : Fin (M.n+1), ((virtualRelease (D 0 [i.val]) (r 0 [i.val]) (columns 0 [i.val]) (u 0)-1)*
      virtualOuterResidual M rM macroColumns i z.fst+
      virtualPayload D r columns d 0 [i.val] u*virtualOuterSelector M rM macroColumns i z.fst))+
    publicValue ρ R d 0 u

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualJointOuter_continuous (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualJointOuter m M ν D ρ R d K rM r p.1.1 p.1.2 p.2) := by
  let Input := HierarchyData M D × Joint E (Blocks m F)
  have hinner : Continuous (fun p : Input => K • p.2.snd) :=
    ((innerProjection (E:=E) (F:=F) m).continuous.comp continuous_snd).const_smul K
  have hdata : Continuous (fun p : Input => (p.1.2,padded (K • p.2.snd))) :=
    continuous_fst.snd.prodMk ((padded_continuous m).comp hinner)
  have hm := (virtualMacroValue_continuous M ν rM).comp (macroData_continuous m M D)
  have hs (i : Fin (M.n+1)) : Continuous (fun p : Input =>
      (virtualRelease (D 0 [i.val]) (r 0 [i.val]) (p.1.2 0 [i.val]) (padded (K • p.2.snd) 0)-1)*
      virtualOuterResidual M rM p.1.1 i p.2.fst+
      virtualPayload D r p.1.2 d 0 [i.val] (padded (K • p.2.snd))*virtualOuterSelector M rM p.1.1 i p.2.fst) := by
    have hr := (virtualRelease_data_continuous D r 0 [i.val]).comp hdata
    have hres := (virtualOuterResidual_continuous M rM i).comp (macroData_continuous m M D)
    have hp := (virtualPayload_continuous D r d 0 [i.val]).comp hdata
    have hsel := virtualOuterSelector_data_continuous m M D rM i
    exact ((hr.sub continuous_const).mul hres).add (hp.mul hsel)
  have hp := (publicValue_joint_contDiff m ρ R d 0 3).continuous.comp hinner
  exact (hm.add (continuous_finset_sum _ (fun i _ => hs i))).add hp

theorem virtualJointOuter_full (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) (z : Joint E (Blocks m F)) :
    virtualJointOuter m M ν D ρ R d K (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) z=
      jointOuter m M ν D ρ R d K z := by
  simp only [virtualJointOuter,jointOuter,outerObjective,attachment,virtualMacroValue_full,
    virtualOuterResidual_full,virtualOuterSelector_full,virtualPayload_full,fullCounts,fullColumns,
    virtualRelease_full]

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualJointOuter_reframe (m : ℕ) (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E)
    (ν : ℝ) (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ColumnData D) (z : Joint E (Blocks m F)) :
    virtualJointOuter m (reframeNode M UM) ν (reframeGeometry D U) ρ R d K rM r macroColumns columns z=
      virtualJointOuter m M ν D ρ R d K rM r macroColumns columns z := by
  simp only [virtualJointOuter,virtualPayload_reframe,virtualOuterSelector_reframe]
  rfl

end Bilevel.ChiPrefixEvaluation
