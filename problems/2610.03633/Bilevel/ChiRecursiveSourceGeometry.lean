import Bilevel.ChiRecursivePayload
import Bilevel.ChiBoundedChainSourceAmplitude

/-! Actual source scale sequence and framed node geometry, including the
special base resolution 1/K and arbitrary nondecreasing curvature ratios. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiBoundedChain

structure Scale where
  curvature : ℝ
  width : ℝ

def Scale.energy (s : Scale) : ℝ := s.curvature*s.width^2
def Scale.force (s : Scale) : ℝ := s.curvature*s.width

def nextScale (s : Scale) (r η : ℝ) : Scale := ⟨r*s.curvature,η*s.width/r⟩

def parentScale (initial : Scale) (r η : ℕ → ℝ) : ℕ → Scale
  | 0 => initial
  | j+1 => nextScale (parentScale initial r η j) (r j) (η j)

def resolution (η K : ℝ) (j : ℕ) : ℝ := if j=0 then 1/K else η

theorem parentScale_positive (initial : Scale) (r η : ℕ → ℝ)
    (hl : 0 < initial.curvature) (hh : 0 < initial.width)
    (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j) (j : ℕ) :
    0<(parentScale initial r η j).curvature ∧ 0<(parentScale initial r η j).width := by
  induction j with
  | zero => exact ⟨hl,hh⟩
  | succ j ih =>
    have hr0 : 0<r j := lt_of_lt_of_le (by norm_num) (hr j)
    exact ⟨mul_pos hr0 ih.1,div_pos (mul_pos (hη j) ih.2) hr0⟩

theorem parentScale_force_succ (initial : Scale) (r η : ℕ → ℝ)
    (hr : ∀ j,1≤r j) (j : ℕ) :
    (parentScale initial r η (j+1)).force=η j*(parentScale initial r η j).force := by
  have hr0 : 0<r j := lt_of_lt_of_le (by norm_num) (hr j)
  simp only [parentScale,nextScale,Scale.force]
  field_simp
  ring

theorem parentScale_energy_succ (initial : Scale) (r η : ℕ → ℝ)
    (hr : ∀ j,1≤r j) (j : ℕ) :
    (parentScale initial r η (j+1)).energy=(η j)^2/(r j)*(parentScale initial r η j).energy := by
  exact source_energy_ratio (hr j)

theorem parentScale_energy_contract (initial : Scale) (r η : ℕ → ℝ)
    (hl : 0 < initial.curvature) (hh : 0 < initial.width) (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j)
    {ηmax : ℝ} (hηmax : ∀ j,η j≤ηmax) (j : ℕ) :
    (parentScale initial r η (j+1)).energy≤ηmax^2*(parentScale initial r η j).energy := by
  have hp := parentScale_positive initial r η hl hh hr hη j
  have hsq : (η j)^2≤ηmax^2 := by have he := hηmax j;have he0 := hη j;nlinarith
  exact (source_energy_ratio_le hp.1.le (hr j)).trans
    (mul_le_mul_of_nonneg_right hsq (show 0≤(parentScale initial r η j).energy by
      exact mul_nonneg hp.1.le (sq_nonneg _)))

theorem base_resolution_positive {η K : ℝ} (hη : 0<η) (hK : 0<K) (j : ℕ) :
    0<resolution η K j := by unfold resolution;split_ifs <;> positivity

theorem base_resolution_le {η K : ℝ} (hK : 0<K) (hthreshold : 1/η≤K) (hη : 0<η) (j : ℕ) :
    resolution η K j≤η := by
  unfold resolution
  split_ifs
  · apply (div_le_iff₀ hK).mpr
    have hh := (div_le_iff₀ hη).mp hthreshold
    nlinarith only [hh]
  · exact le_rfl

theorem source_force_formula (initial : Scale) (r : ℕ → ℝ) (hr : ∀ j,1≤r j)
    (η K : ℝ) (j : ℕ) :
    (parentScale initial r (resolution η K) (j+1)).force=η^j*(initial.force/K) := by
  induction j with
  | zero =>
    rw [parentScale_force_succ initial r _ hr]
    simp only [resolution,if_pos rfl,ite_true,parentScale,pow_zero,one_mul]
    ring
  | succ j ih =>
    rw [parentScale_force_succ initial r _ hr,ih]
    simp only [resolution,if_neg (Nat.succ_ne_zero j),pow_succ]
    ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def sourceNode (A Kminus ζ cn η CR lp hp r b : ℝ)
    (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] E) : Node E where
  n := sourceChainIndex cn r η
  ell := r*lp
  width := η*hp/r
  receiver := A
  nu := ζ*lp
  force := η*(lp*hp)
  parentWidth := hp
  tailRadius := Kminus*(η*(lp*hp))/(ζ*lp)
  radius := sourceLocalRadius CR lp hp r b ζ
  frame := U

def sourceGeometry (initial : Scale) (r η b : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (U : ∀ j, List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] E) : Geometry E :=
  fun j I => sourceNode A Kminus ζ cn (η j) CR (parentScale initial r η j).curvature
    (parentScale initial r η j).width (r j) (b j) (U j I)

omit [CompleteSpace E] in
theorem sourceGeometry_energy (initial : Scale) (r η b : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (U : ∀ j, List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] E) (j : ℕ) (I : List ℕ) :
    (sourceGeometry initial r η b A Kminus ζ cn CR U j I).ell*
      (sourceGeometry initial r η b A Kminus ζ cn CR U j I).width^2=
      (parentScale initial r η (j+1)).energy := rfl

omit [CompleteSpace E] in
theorem sourceGeometry_force (initial : Scale) (r η b : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (U : ∀ j, List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] E) (j : ℕ) (I : List ℕ) :
    (sourceGeometry initial r η b A Kminus ζ cn CR U j I).ell*
      (sourceGeometry initial r η b A Kminus ζ cn CR U j I).width=
      (parentScale initial r η (j+1)).force := rfl

end Bilevel.ChiRecursive
