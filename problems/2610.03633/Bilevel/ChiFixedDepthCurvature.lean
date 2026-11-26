import Bilevel.ChiOuterUpperTrace
import Bilevel.ChiOuterSourceUpperBase
import Bilevel.ChiLinearJetContraction
import Bilevel.ChiOuterExtensionTrace

/-! Actual full-objective curvature at fixed recursive depth one.
The bound is independent of both chain lengths and all frame dimensions. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper ChiExtensionCalibration
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem fixed_outer_second_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (Bu Bc : ℝ) (hρ : 0≤ρ 1) (hR : 0<R 1)
    (hu : ∀ z,‖iteratedFDeriv ℝ 2 (upperBase m M ν D 1 (ρ 0) (R 0)) z‖≤Bu)
    (hc : ∀ z,‖iteratedFDeriv ℝ 2 (outerCarrier m M D 1 1) z‖≤Bc)
    (z : Joint E (Blocks m F)) :
    ‖iteratedFDeriv ℝ 2 (jointOuter m M ν D ρ R 1 1) z‖≤Bu+Bc+ρ 1 := by
  let Q := hierarchyBlock (E:=E) (F:=F) m 1
  have hQ : ‖Q‖≤1 := hierarchyBlock_norm_le m 1
  have hbc : ContDiff ℝ 3 (bowl (ρ 1) (R 1) : F → ℝ) := full_bowl_contDiff _ _ 3
  have hb : ‖iteratedFDeriv ℝ 2 (bowl (ρ 1) (R 1) ∘ Q) z‖≤ρ 1 :=
    (linear_jet_contraction Q hQ hbc z 2 (by norm_num)).trans
      (Regularity.bowl_jet_two _ _ hρ hR _)
  have he : jointOuter m M ν D ρ R 1 1=
      fun x => (upperBase m M ν D 1 (ρ 0) (R 0) x+outerCarrier m M D 1 1 x)+
        (bowl (ρ 1) (R 1) ∘ Q) x := by
    funext x
    simpa only [Fin.sum_univ_one,Fin.val_zero,Nat.zero_add] using upperBase_trace m M ν D ρ R 1 x
  have huC := upperBase_contDiff m M ν D 1 (ρ 0) (R 0)
  have hcC := outerCarrier_contDiff m M D 1 1
  have hbC := hbc.comp Q.contDiff
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  rw [he,iteratedFDeriv_add_apply' (((huC.add hcC).of_le h23).contDiffAt)
    ((hbC.of_le h23).contDiffAt),
    iteratedFDeriv_add_apply' ((huC.of_le h23).contDiffAt) ((hcC.of_le h23).contDiffAt)]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add (hu z) (hc z))) hb)

theorem source_fixed_objective_second (A K ζ cn CR Km : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ),(∀ j,1≤r j) → r 0=1 → r 1=1 →
      (∀ j,0<η j) → (∀ j,η j≤1) → (∀ j,128≤cn/(η j)^2) →
      (∀ j,0<b j) → (∀ j,b j≤1) →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      let rad := fun j => b j*(D j []).nu
      let R := fun j => (D j []).radius
      ∀ (m : ℕ) (z : Joint E (Blocks m F)),
      ‖iteratedFDeriv ℝ 2 (jointOuter m M (initial.curvature/24) D rad R 1 1) z‖≤C*initial.curvature := by
  obtain ⟨Cu,hCu,hupper⟩ := source_upper_base_budgets A K ζ cn CR Km
    hA hK hζ hζ1 hcn hcn1 hCR hCRcn hKm
  obtain ⟨Cc,hCc,hcarrier⟩ := source_outer_selected_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  let C := Cu+Cc^3+1
  have hCc0 : 0≤Cc := by linarith
  have hC : 1≤C := by dsimp [C]; nlinarith [pow_nonneg hCc0 3]
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hw r η b hr hr0 hr1 hη hη1 hlen hb hb1 U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  let rad := fun j => b j*(D j []).nu
  let R := fun j => (D j []).radius
  have hp := parentScale_positive initial r η hl hw hr hη
  have hell : (D 1 []).ell=initial.curvature := by
    simp only [D,sourceGeometry,ChiRecursive.sourceNode,parentScale,nextScale,hr0,hr1,one_mul]
  have hnu : (D 1 []).nu=ζ*initial.curvature := by
    simp only [D,sourceGeometry,ChiRecursive.sourceNode,parentScale,nextScale,hr0,one_mul]
  have hrad : 0≤rad 1 := by dsimp [rad]; rw [hnu]; exact mul_nonneg (hb 1).le (mul_pos hζ hl).le
  have hradle : rad 1 ≤ initial.curvature := by
    have hh := mul_le_mul (hb1 1) hζ1 hζ.le zero_le_one
    have hm := mul_le_mul_of_nonneg_right hh hl.le
    dsimp [rad]
    rw [hnu]
    nlinarith only [hm]
  have hnode := sourceNode_admissible A K ζ cn (η 1) CR
    (parentScale initial r η 1).curvature (parentScale initial r η 1).width
    (r 1) (b 1) (V 1 []) hK hζ hζ1 (hη 1) (hη1 1) hCR (hp 1).1 (hp 1).2
    (hr 1) (hb 1) (hb1 1)
  have hR : 0<R 1 := hnode.2.1.trans_le hnode.2.2.1
  have hu := hupper E F n initial hl hw r η b hr hr0 hη hη1 hlen hb hb1 U V
  have hc := hcarrier E F n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  intro m z
  have hh := fixed_outer_second_bound m M (initial.curvature/24) D rad R
    (Cu*initial.curvature) (Cc^3*initial.curvature) hrad hR (fun x => (hu 1 m x).1)
    (fun x => by
      have hx := hc 1 1 m x 2 (by norm_num)
      change ‖iteratedFDeriv ℝ 2 (outerCarrier m M D 1 1) x‖≤Cc^3*(D 1 []).ell at hx
      rwa [hell] at hx) z
  apply hh.trans
  dsimp [C]
  nlinarith only [hradle]

end Bilevel.ChiOuter
