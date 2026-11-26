import HardFamilyBayesRisk

open MeasureTheory

namespace Task006.HardFamilyBayes

open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereGlobal
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStoppedCoupling

noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def finalRank (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) : ℕ := (jointFrame alg k hkd N j w).1.val

theorem finalRank_measurable (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    Measurable (finalRank alg k hkd j) := by
  have hv : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  exact hv.comp (measurable_fst.comp (jointFrame_measurable alg k hkd N j))

theorem finalRank_le_twice_originalK (alg : OracleAlgorithm d N S) (R : ℝ)
    (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) :
    finalRank alg k hkd j w ≤ 2*originalK alg j w := by
  have hcap := (hlegal (column w.2 j) ((orthonormal_column w.2).norm_eq_one j) w.1.1 w.1.2).2.1
  exact stopped_frame_rank_le_twice_original_informative alg w.1.2 w.1.1 k hkd (column w.2 j) hcap

theorem goodRankEvent_half_mass (alg : OracleAlgorithm d N S)
    (L R A : ℝ) (hL : 0 < L) (hA : 16 ≤ A) (hlegal : LegalOriginal alg R)
    (σ : Measure S) [IsProbabilityMeasure σ] (k : ℕ) (hkd : k ≤ d) (hk : 0 < k)
    (hdk : d ≤ 8*k) (j : Fin d) (hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32) :
    (1/2 : ℝ) ≤ ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)).real
      (goodRankEvent alg k hkd j) := by
  have hreal : Measurable (fun w : Exogenous S × OrthogonalGroup d =>
      (finalRank alg k hkd j w : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (finalRank_measurable alg k hkd j)
  have hm := Task006.LowerEventMass.rank_lt_threshold_half_mass
    (μ := (σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d))
    (fun w => (originalK alg j w : ℝ)) (fun w => (finalRank alg k hkd j w : ℝ)) d k
    (originalK_integrable alg j _) (fun _ => Nat.cast_nonneg _) hreal
    (by exact_mod_cast hk) (by exact_mod_cast hdk)
    ((originalK_expectation alg j L A hL hA σ).trans hbudget)
    (fun w => by exact_mod_cast finalRank_le_twice_originalK alg R hlegal k hkd j w)
  have he : {w : Exogenous S × OrthogonalGroup d | (finalRank alg k hkd j w : ℝ) < (k : ℝ)} =
      goodRankEvent alg k hkd j := by
    ext w
    change ((finalRank alg k hkd j w : ℝ) < (k : ℝ)) ↔ finalRank alg k hkd j w < k
    exact Nat.cast_lt
  rw [he] at hm
  exact hm

theorem goodRankEvent_small_mass (alg : OracleAlgorithm d N S)
    (L R A : ℝ) (hL : 0 < L) (hA : 16 ≤ A) (hlegal : LegalOriginal alg R)
    (σ : Measure S) [IsProbabilityMeasure σ] (h1d : 1 ≤ d) (hd7 : d ≤ 7)
    (j : Fin d) (hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32) :
    (25/32 : ℝ) ≤ ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)).real
      (goodRankEvent alg 1 h1d j) := by
  have hb : (∫ w, (originalK alg j w : ℝ)
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) ≤ 7/32 := by
    have he := (originalK_expectation alg j L A hL hA σ).trans hbudget
    have hd : (d : ℝ) ≤ 7 := by exact_mod_cast hd7
    linarith
  have hm := Task006.LowerEventMass.rank_zero_small_dimension_mass
    (μ := (σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d))
    (originalK alg j) (finalRank alg 1 h1d j)
    (originalK_integrable alg j _) (finalRank_measurable alg 1 h1d j) hb
    (finalRank_le_twice_originalK alg R hlegal 1 h1d j)
  have he : {w : Exogenous S × OrthogonalGroup d | finalRank alg 1 h1d j w = 0} =
      goodRankEvent alg 1 h1d j := by
    ext w
    change finalRank alg 1 h1d j w = 0 ↔ finalRank alg 1 h1d j w < 1
    omega
  rw [he] at hm
  exact hm

end
end Task006.HardFamilyBayes
