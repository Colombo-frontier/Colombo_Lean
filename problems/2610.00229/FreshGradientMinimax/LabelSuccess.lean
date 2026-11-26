import FreshGradientMinimax.LabelDimension

/-! Pointwise testing obstruction for the two true signed hard objectives.
The output can be arbitrary and need never have been queried: B.1 supplies the
global disjoint success regions, and the full transcript coupling supplies
output equality on the good event. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem truthValue_disjoint {P Q : Prop} (h : ¬ (P ∧ Q)) : truthValue P + truthValue Q ≤ 1 := by
  classical
  by_cases hp : P <;> by_cases hq : Q
  · exact False.elim (h ⟨hp, hq⟩)
  · simp [truthValue, hp, hq]
  · simp [truthValue, hp, hq]
  · simp [truthValue, hp, hq]

namespace Algorithm
variable {D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 D Seed)

def labelActualOutput (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) (s : ℝ) (hs : s ^ 2 = 1) (seed : Seed) : Euclid 1 :=
  A.output N (A.deterministicRun
    (fun _ => (pathHorizonObjective p hκ N (labelFrame hD z) s hs).jointGradient) N seed)

def labelSuccessIndicator (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) (s : ℝ) (hs : s ^ 2 = 1) (seed : Seed) : ℝ :=
  truthValue (A.labelActualOutput p hκ N hD z s hs seed ∈
    (pathHorizonObjective p hκ N (labelFrame hD z) s hs).successSet p.ε)

def labelPairSuccess (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) (seed : Seed) : ℝ :=
  (A.labelSuccessIndicator p hκ N hD z 1 (by norm_num) seed +
    A.labelSuccessIndicator p hκ N hD z (-1) (by norm_num) seed) / 2

theorem labelPairSuccess_coupling (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    (N : ℕ) (hD : 4 * N + 4 ≤ D) (z : Fin (4 * N + 4) → Fin D) (seed : Seed) :
    A.labelPairSuccess p hκ N hD z seed ≤ 1 / 2 + truthValue (¬ A.LabelGood p N z seed) := by
  classical
  by_cases hg : A.LabelGood p N z seed
  · have hp := A.labelGood_output_identity p hκ N hD z seed (by norm_num : (1 : ℝ) ^ 2 = 1) hg
    have hn := A.labelGood_output_identity p hκ N hD z seed (by norm_num : (-1 : ℝ) ^ 2 = 1) hg
    have hd := pathHorizonObjective_success_disjoint p hκ N (labelFrame hD z) (labelFrame hD z)
    have he : ¬ (A.output N (A.deterministicRun (labelAuxiliaryReply p N z) N seed) ∈
        (pathHorizonObjective p hκ N (labelFrame hD z) 1 (by norm_num)).successSet p.ε ∧
      A.output N (A.deterministicRun (labelAuxiliaryReply p N z) N seed) ∈
        (pathHorizonObjective p hκ N (labelFrame hD z) (-1) (by norm_num)).successSet p.ε) := by
      rintro ⟨hpos, hneg⟩
      exact Set.disjoint_left.mp hd hpos hneg
    have hb := truthValue_disjoint he
    unfold labelPairSuccess labelSuccessIndicator labelActualOutput
    rw [hp, hn]
    have hz : truthValue (¬ A.LabelGood p N z seed) = 0 := by simp [truthValue, hg]
    rw [hz]
    linarith
  · have hp := truthValue_le_one (A.labelActualOutput p hκ N hD z 1 (by norm_num) seed ∈
      (pathHorizonObjective p hκ N (labelFrame hD z) 1 (by norm_num)).successSet p.ε)
    have hn := truthValue_le_one (A.labelActualOutput p hκ N hD z (-1) (by norm_num) seed ∈
      (pathHorizonObjective p hκ N (labelFrame hD z) (-1) (by norm_num)).successSet p.ε)
    have hz : truthValue (¬ A.LabelGood p N z seed) = 1 := by simp [truthValue, hg]
    rw [hz]
    unfold labelPairSuccess labelSuccessIndicator
    linarith

end Algorithm

theorem Algorithm.labelPairSuccess_average (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 (labelHidingDimension p N) Seed) (seed : Seed) :
    (𝔼 z : Fin (4 * N + 4) → Fin (labelHidingDimension p N),
      A.labelPairSuccess p hκ N (labelHidingDimension_size p N) z seed) ≤ (7 / 12 : ℝ) := by
  have hc := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ :
      Finset (Fin (4 * N + 4) → Fin (labelHidingDimension p N)))) =>
    A.labelPairSuccess_coupling p hκ N (labelHidingDimension_size p N) z seed)
  rw [Finset.expect_add_distrib, Fintype.expect_const] at hc
  have hb := A.labelBad_one_twelfth p N seed
  linarith

end FreshGradientMinimax
