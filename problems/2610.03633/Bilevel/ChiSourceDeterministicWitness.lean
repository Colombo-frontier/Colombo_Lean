import Bilevel.ChiSourcePrimitive
import Bilevel.ChiSourceMacroObjective
import Bilevel.ChiPrimitiveObjective

/-! Actual deterministic source witness with exact public primitive
budgets, attained unique response, prescribed initial gap, and the blind
macro gradient barrier. Random frames and oracle hiding are separate. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule
open scoped RealInnerProductSpace
universe u

def sourceCoarseNormal (J : ℕ) (i : Fin J) : Fin (2*J) := ⟨i.val,by omega⟩
def sourceRadialNormal (J : ℕ) (i : Fin J) : Fin (2*J) := ⟨J+i.val,by omega⟩
def sourceFineNormal (J : ℕ) (hJ : 1 ≤ J) : Fin (2*J) := ⟨J-1,by omega⟩

theorem sourceCoarseNormal_injective (J : ℕ) : Function.Injective (sourceCoarseNormal J) := by
  intro i j h
  have hh := congrArg (fun x : Fin (2*J) => x.val) h
  exact Fin.ext hh

theorem sourceRadialNormal_injective (J : ℕ) : Function.Injective (sourceRadialNormal J) := by
  intro i j h
  have hh := congrArg Fin.val h
  apply Fin.ext
  dsimp only [sourceRadialNormal] at hh
  omega

theorem source_normal_disjoint (J : ℕ) (i j : Fin J) : sourceCoarseNormal J i ≠ sourceRadialNormal J j := by
  intro h
  have hh := congrArg Fin.val h
  dsimp only [sourceCoarseNormal,sourceRadialNormal] at hh
  omega

set_option maxHeartbeats 1600000 in
theorem source_deterministic_witness :
    ∃ t η ζ cn CR Km Cgap η₀ Cf CT Cacc c : ℝ,
      0 < t ∧ t < 1 ∧ 0 < η ∧ η ≤ 1 ∧ 0 < ζ ∧ ζ ≤ 2/15 ∧ 0 < cn ∧ cn ≤ 1 ∧
      128 ≤ cn/η^2 ∧ 1 ≤ CR ∧ ζ*Real.sqrt cn ≤ CR ∧ 1 ≤ Km ∧ 1 ≤ Cgap ∧
      0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ θ Δ ε : ℝ),
      0 < L → 0 < μ → 2*μ ≤ L → κ=L/μ → θ ≤ κ → sourceBranchThreshold CT η ≤ θ →
      0 < Δ → 0 < ε → ε ≤ accuracyWindow c Cacc L κ θ Δ (ChiIndependentWidths.chosenDepth θ) 6 →
      let J := ChiIndependentWidths.chosenDepth θ
      let T := scale θ CT 6
      let initial : Scale := ⟨η₀*L,sourceWidth (32/t) ε η₀ L t η J⟩
      let n := macroIndex Δ Cgap initial.energy
      ∃ hJ : 1 ≤ J,128 ≤ n ∧
      η₀*L*Δ*(t*η)^(2*J)/(4*Cgap*(32/t)^2*ε^2) ≤ (n:ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1 ≤ v, ∃ hwidth : ∀ j I,0 < (D j I).width,
      let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let hExt := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖ ≤ (1:ℝ)/12,
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        ∀ x,M.coordinates x.fst (Fin.last n) < initial.width → 8*ε ≤ ‖gradient (P.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hmacro⟩ :=
    source_macro_objective_certificate.{u}
  have hCb : 0 < 32/t := by positivity
  have hζ1 : ζ ≤ 1 := by linarith
  obtain ⟨η₀,Cf,CT,Cold,cold,hη₀,hη₀1,hCf,hCT,hCold,hcold,hcold1,hprimitive⟩ :=
    source_primitive_certificate (A:=3) (Kminus:=1) (Cb:=32/t) (cms:=1/128)
      (by norm_num) (by norm_num) hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCb ht (by norm_num) (by norm_num)
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hobjective⟩ := hmacro η₀ (32/t) Cold cold hη₀ le_rfl hCold hcold
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,Cf,CT,Cacc,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hCf,hCT,hCacc,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ θ Δ ε hL hμ hμL hκeq hθκ hbranch hΔ hε hwindow
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  let T := scale θ CT 6
  let initial : Scale := ⟨η₀*L,sourceWidth (32/t) ε η₀ L t η J⟩
  let n := macroIndex Δ Cgap initial.energy
  let weight := fun j : ℕ => t^(j+1)
  have hbranches := source_branch_conditions hCT hbranch hθκ
  have hθ : 1 ≤ θ := hbranches.1
  have hκ : 1 ≤ κ := hθ.trans hθκ
  have hJ : 1 ≤ J := hbranches.2.1
  have hT : 1 ≤ T := (by norm_num : (1:ℝ) ≤ 2).trans hbranches.2.2.2.2
  have ho := hobjective E F J L κ θ Δ ε T hL hκ hθ hΔ hε hT hbranches.2.2.1 hwindow
  have hp := hprimitive E F n L μ κ θ Δ ε weight hL hμ hμL hκeq hθκ hbranch hε ho.1
    (fun j => pow_pos ht _) (fun j => pow_le_one₀ ht.le ht1.le)
  refine ⟨hJ,ho.2.1,ho.2.2.1,?_⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight 3 1 ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let obj := jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6)
  obtain ⟨hv,hwidth,hp'⟩ := hp U V
  obtain ⟨hb,P,hf,hg,r,hr,hmean,hunique⟩ := hp' (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
  have ho' := ho.2.2.2 U V
  have hcont : Continuous obj := (jointOuter_contDiff (J+1) M (initial.curvature/24) D rad R J (κ/6) 0).continuous
  have hgap := ChiPrimitive.gapCertificate_of_coercive_mean P r obj hcont ho'.1 hmean 0 Δ ho'.2.2.1
  refine ⟨hv,hwidth,hb,P,hf,hg,r,hgap,hr,hmean,hunique,?_,?_⟩
  · exact (hmean 0).trans ho'.2.1
  · intro x hlast
    rw [ChiPrimitive.mean_gradient_eq P r obj hmean x]
    exact ho'.2.2.2 x hlast

end Bilevel.ChiExtensionCalibration
