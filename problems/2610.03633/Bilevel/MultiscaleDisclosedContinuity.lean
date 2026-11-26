import Bilevel.MultiscaleDisclosedPotentials
import Bilevel.ChiRecursiveJointObjective

/-! Joint continuity of the literal disclosed scalar potentials, including
arbitrary invalid finite arrays. No orthonormal completion is selected. -/
noncomputable section
namespace Bilevel.MultiscaleMean.Parameters
open CompensatedMean ChiPrefixEvaluation ZeroChainSchedule SmallGapProfiles
set_option autoImplicit false
set_option maxHeartbeats 160000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (P : Parameters (E:=E) n)

theorem disclosedResidual_continuous (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => P.disclosedResidual r p.1 p.2) :=
  disclosedEvaluator_continuous n r P.R _ (ZeroChainResidualScaled.R_contDiff n P.amplitude P.β).continuous

theorem disclosedFlat_continuous (δ : ℝ) (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => P.disclosedFlat δ r p.1 p.2) :=
  disclosedEvaluator_continuous n r P.R _
    (ZeroChainFlatteningBounds.flattenedResidual_contDiff n P.amplitude P.β δ).continuous

theorem disclosedRevealed_continuous (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × E => P.disclosedRevealed r p.1 p.2) :=
  (disclosedEvaluator_continuous n r P.R _
    (ZeroChainResidualScaled.A_contDiff n P.amplitude P.β).continuous).add
    ((ChiRecursive.full_bowl_contDiff P.ν P.R 3).continuous.comp continuous_snd)

theorem disclosedPerturbation_continuous (active : Bool) (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × LowerSpace E => P.disclosedPerturbation active r p.1 p.2) := by
  have hu : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E => uProj E p.2) :=
    (uProj E).continuous.comp continuous_snd
  have hs : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E => sProj E p.2) :=
    (sProj E).continuous.comp continuous_snd
  have hz : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E =>
      if active then P.disclosedResidual r p.1 (uProj E p.2)
      else P.disclosedFlat P.signalResolution r p.1 (uProj E p.2)) := by
    cases active
    · have h := (P.disclosedFlat_continuous P.signalResolution r).comp (continuous_fst.prodMk hu)
      simpa only [Bool.false_eq_true,if_false,Function.comp_apply] using h
    · have h := (P.disclosedResidual_continuous r).comp (continuous_fst.prodMk hu)
      simpa only [if_true,Function.comp_apply] using h
  have hq (j : ℕ) : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E =>
      normal (width P.c P.β P.θ j) (sProj E p.2)) :=
    ((normal_contDiff _ (width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j)).continuous).comp hs
  have hfinal : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E =>
      normal P.finalWidth (sProj E p.2)) :=
    (normal_contDiff _ P.finalWidth_pos).continuous.comp hs
  have hsum : Continuous (fun p : (Fin (n+1) → E) × LowerSpace E =>
      ∑ j ∈ Finset.range (levels P.θ),P.disclosedFlat (resolution P.c P.β P.θ j) r p.1 (uProj E p.2)*
        (normal (width P.c P.β P.θ j) (sProj E p.2)-normal (width P.c P.β P.θ (j+1)) (sProj E p.2))) := by
    apply continuous_finset_sum
    intro j _
    exact ((P.disclosedFlat_continuous _ r).comp (continuous_fst.prodMk hu)).mul ((hq j).sub (hq (j+1)))
  have hc1 : Continuous (fun _ : (Fin (n+1) → E) × LowerSpace E => P.μ/(2*P.L^2)) := continuous_const
  have hc2 : Continuous (fun _ : (Fin (n+1) → E) × LowerSpace E => P.μ/P.L) := continuous_const
  have hh := (hc1.mul (hz.pow 2)).sub (hc2.mul ((hz.mul hfinal).add hsum))
  exact hh

theorem quadraticPart_continuous :
    Continuous (fun q : E × LowerSpace E => P.quadraticPart q.1 q.2) := by
  have hu : Continuous (fun q : E × LowerSpace E => uProj E q.2) :=
    (uProj E).continuous.comp continuous_snd
  have hs : Continuous (fun q : E × LowerSpace E => sProj E q.2) :=
    (sProj E).continuous.comp continuous_snd
  have hz : Continuous (fun q : E × LowerSpace E => zProj E q.2) :=
    (zProj E).continuous.comp continuous_snd
  exact ((continuous_const.mul ((hu.norm.pow 2).add (hs.pow 2))).add
    (continuous_const.mul (hz.pow 2))).sub (continuous_const.mul (continuous_fst.inner hu))

theorem disclosedUpper_continuous (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) =>
      P.disclosedUpper r p.1 p.2.1 p.2.2) := by
  have hu : Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) => uProj E p.2.2) :=
    (uProj E).continuous.comp (continuous_snd.comp continuous_snd)
  have hs : Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) => sProj E p.2.2) :=
    (sProj E).continuous.comp (continuous_snd.comp continuous_snd)
  exact ((P.disclosedRevealed_continuous r).comp (continuous_fst.prodMk hu)).add (continuous_const.mul hs)

theorem disclosedLower_continuous (active : Bool) (r : ℕ) :
    Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) =>
      P.disclosedLower active r p.1 p.2.1 p.2.2) := by
  have hq : Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) =>
      P.quadraticPart p.2.1 p.2.2) := P.quadraticPart_continuous.comp continuous_snd
  have hargs : Continuous (fun p : (Fin (n+1) → E) × (E × LowerSpace E) => (p.1,p.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hp := (P.disclosedPerturbation_continuous active r).comp hargs
  exact hq.add hp

end Bilevel.MultiscaleMean.Parameters
