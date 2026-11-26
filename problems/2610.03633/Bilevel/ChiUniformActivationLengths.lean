import Bilevel.ChiScheduledNodeScales
import Bilevel.ChiUniformWidthCalibration

/-! Actual finite chain lengths and their telescoping product. These are
counts of encoded source coordinates; query accounting is separate. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiIndependentWidths
open ChiCurvatureSchedule ChiExtensionCalibration ChiRecursive ChiBoundedChain

def higherCount (cn η T : ℝ) (J : ℕ) : ℕ :=
  ∏ j ∈ Finset.range J,length cn η T j

def activationCount (cS cn Δ L₀ b h η T : ℝ) (J : ℕ) : ℕ :=
  macroLength cS Δ L₀ b*middleLength cn b h*higherCount cn η T J

def sourceIndexCount (cn η T Kg : ℝ) (J : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (J+1),(sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1)

theorem curvature_ratio_product {T : ℝ} (hT : 0<T) (J : ℕ) :
    (∏ j ∈ Finset.range J,curvature T (j+1)/curvature T j)=curvature T J := by
  induction J with
  | zero => simp [curvature_zero]
  | succ J ih =>
    rw [Finset.prod_range_succ,ih]
    have ha := (curvature_pos hT J).ne'
    field_simp

theorem higher_length_half_lower {cn η T : ℝ} (hcn : 0≤cn) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (j : ℕ) :
    (cn/(2*η^2))*(curvature T (j+1)/curvature T j)≤(length cn η T j:ℝ) := by
  have harg : 128≤cn*(curvature T (j+1)/curvature T j)/η^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg η)
    have hm := mul_le_mul_of_nonneg_left (curvature_ratio_ge_one hT j) hcn
    simpa only [mul_one] using hm
  have hh := LowerAlgebra.natFloor_half_lower _ (show 2≤cn*(curvature T (j+1)/curvature T j)/η^2 by linarith only [harg])
  convert hh using 1
  ring

theorem higherCount_lower {cn η T : ℝ} (hcn : 0≤cn) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (J : ℕ) :
    (cn/(2*η^2))^J*curvature T J≤(higherCount cn η T J:ℝ) := by
  induction J with
  | zero => simp [higherCount,curvature_zero]
  | succ J ih =>
    have hl := higher_length_half_lower hcn hT hlen J
    have hn : 0≤(cn/(2*η^2))*(curvature T (J+1)/curvature T J) := by
      exact mul_nonneg (div_nonneg hcn (by positivity))
        (div_nonneg (curvature_pos (lt_of_lt_of_le zero_lt_one hT) (J+1)).le
          (curvature_pos (lt_of_lt_of_le zero_lt_one hT) J).le)
    have hm := mul_le_mul ih hl hn (Nat.cast_nonneg _)
    have he : ((cn/(2*η^2))^J*curvature T J)*
        ((cn/(2*η^2))*(curvature T (J+1)/curvature T J))=
        (cn/(2*η^2))^(J+1)*curvature T (J+1) := by
      have ha := (curvature_pos (lt_of_lt_of_le zero_lt_one hT) J).ne'
      have hc : curvature T J*(curvature T (J+1)/curvature T J)=curvature T (J+1) := by
        field_simp
      calc
        _ = ((cn/(2*η^2))^J*(cn/(2*η^2)))*
          (curvature T J*(curvature T (J+1)/curvature T J)) := by ring
        _ = _ := by rw [hc,pow_succ (cn/(2*η^2)) J]
    rw [he] at hm
    simpa only [higherCount,Finset.prod_range_succ,Nat.cast_mul] using hm

theorem source_base_length {cn b h η T : ℝ} (_hb : 0<b) (hh : 0<h)
    (hn : 1≤middleLength cn b h) :
    sourceChainIndex cn (sourceRatio T 0) (resolution η (b/h) 0)+1=middleLength cn b h := by
  have he : Nat.floor (cn*sourceRatio T 0/(resolution η (b/h) 0)^2)=middleLength cn b h := by
    unfold middleLength
    congr 1
    simp only [sourceRatio,resolution,if_pos rfl]
    field_simp
  unfold sourceChainIndex
  rw [he]
  omega

theorem source_higher_length {cn η T : ℝ} (hcn : 0≤cn) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (Kg : ℝ) (j : ℕ) :
    sourceChainIndex cn (sourceRatio T (j+1)) (resolution η Kg (j+1))+1=length cn η T j := by
  unfold sourceChainIndex
  rw [source_high_length]
  have hh := length_large hcn hT hlen j
  omega

theorem sourceIndexCount_eq {cn b h η T : ℝ} (hcn : 0≤cn) (hb : 0<b) (hh : 0<h)
    (hT : 1≤T) (hlen : 128≤cn/η^2) (hn : 1≤middleLength cn b h) (J : ℕ) :
    sourceIndexCount cn η T (b/h) J=middleLength cn b h*higherCount cn η T J := by
  unfold sourceIndexCount
  rw [Finset.prod_range_succ']
  rw [source_base_length hb hh hn]
  rw [mul_comm _ (middleLength cn b h)]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact source_higher_length hcn hT hlen (b/h) j

theorem activationCount_source_indices {cS cn Δ L₀ b h η T : ℝ}
    (hcn : 0≤cn) (hb : 0<b) (hh : 0<h) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (hn : 1≤middleLength cn b h) (J : ℕ) :
    activationCount cS cn Δ L₀ b h η T J=
      macroLength cS Δ L₀ b*sourceIndexCount cn η T (b/h) J := by
  rw [sourceIndexCount_eq hcn hb hh hT hlen hn]
  unfold activationCount
  ring

theorem activationCount_lower {cS cn Δ L₀ b h η T : ℝ}
    (hcn : 0<cn) (hL : 0<L₀) (hb : 0<b) (hh : 0<h) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (hmacro : 2≤cS*Δ/(L₀*b^2))
    (hmiddle : 2≤cn*b^2/h^2) (J : ℕ) :
    (cS*cn*Δ/(4*L₀*h^2))*((cn/(2*η^2))^J*curvature T J)≤
      (activationCount cS cn Δ L₀ b h η T J:ℝ) := by
  have hm := stage_count_lower hcn hL hb hh hmacro hmiddle
  have hi := higherCount_lower hcn.le hT hlen J
  have ha := curvature_pos (lt_of_lt_of_le zero_lt_one hT) J
  have hp := mul_le_mul hm hi (show 0≤(cn/(2*η^2))^J*curvature T J by positivity)
    (Nat.cast_nonneg (macroLength cS Δ L₀ b*middleLength cn b h))
  simpa only [activationCount,Nat.cast_mul] using hp

end Bilevel.ChiIndependentWidths
