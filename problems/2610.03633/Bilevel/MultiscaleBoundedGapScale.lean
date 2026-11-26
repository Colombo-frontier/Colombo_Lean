import Bilevel.LowerAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Literal width and natural chain floor for the macro-free all-gap
accuracy window. These are source-parameter inequalities, not query bounds. -/
noncomputable section
namespace Bilevel.MultiscaleMean
set_option autoImplicit false
set_option maxHeartbeats 800000

def innerWidth (A η ε κ L : ℝ) : ℝ := 32*A^2*ε/(η*κ*L)

def innerLength (η L Δ β : ℝ) : ℕ := Nat.floor (Δ/(η*L*β^2))

theorem inner_margin_exact {A η ε κ L : ℝ} (hA : 0<A) (hη : 0<η)
    (hκ : 0<κ) (hL : 0<L) :
    ((L/A)/(2*(L/κ)))*η*(L/A)*innerWidth A η ε κ L/2=8*ε := by
  unfold innerWidth
  field_simp
  ring

theorem inner_scale_certificate {A η τ : ℝ} (hA : 1≤A) (hη : 0<η)
    (hη1 : η≤1) (hτ : 0<τ) :
    ∃ c : ℝ,0<c ∧ c≤1 ∧
    ∀ L Δ κ θ ε : ℝ,0<L → 0<Δ → 0<κ → 1≤θ → θ≤κ → 0<ε →
      ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      let β := innerWidth A η ε κ L
      let T := innerLength η L Δ β
      0<β ∧ β*θ≤τ ∧ 256≤T ∧ T-1+1=T ∧
      (T:ℝ)*η*L*β^2≤Δ ∧
      (η/(2048*A^4))*L*κ^2*Δ/ε^2≤(T:ℝ) := by
  have hAp : 0<A := by linarith
  let c := min 1 (min (τ*η/(32*A^2)) (η/(512*A^2)))
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro L Δ κ θ ε hL hΔ hκ hθ hθκ hε hacc
  dsimp only
  let β := innerWidth A η ε κ L
  let T := innerLength η L Δ β
  have hβ : 0<β := by dsimp [β,innerWidth]; positivity
  have hcτ : c≤τ*η/(32*A^2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcΔ : c≤η/(512*A^2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hεL : ε≤(τ*η/(32*A^2))*L :=
    (hacc.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le)).trans
      (mul_le_mul_of_nonneg_right hcτ hL.le)
  have hεΔ : ε≤(η/(512*A^2))*(κ*Real.sqrt (L*Δ)) :=
    (hacc.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le)).trans
      (mul_le_mul_of_nonneg_right hcΔ (by positivity))
  have hβθ : β*θ≤τ := by
    have hh := mul_le_mul_of_nonneg_left hεL
      (show 0≤32*A^2/(η*L) by positivity)
    have he : (32*A^2/(η*L))*((τ*η/(32*A^2))*L)=τ := by field_simp; ring
    rw [he] at hh
    have hbκ : β*κ=(32*A^2/(η*L))*ε := by
      dsimp [β,innerWidth]
      field_simp
      ring
    exact (mul_le_mul_of_nonneg_left hθκ hβ.le).trans (hbκ ▸ hh)
  have hβroot : β≤Real.sqrt (L*Δ)/(16*L) := by
    have hh := mul_le_mul_of_nonneg_left hεΔ
      (show 0≤32*A^2/(η*κ*L) by positivity)
    convert hh using 1
    all_goals dsimp [β,innerWidth]
    all_goals field_simp
    all_goals ring
  have hβsq : 256*L*β^2≤Δ := by
    have hh := (le_div_iff₀ (by positivity : 0<16*L)).mp hβroot
    have hs := pow_le_pow_left₀ (show 0≤β*(16*L) by positivity) hh 2
    rw [Real.sq_sqrt (mul_pos hL hΔ).le] at hs
    have hh' : L*(256*L*β^2)≤L*Δ := by nlinarith only [hs]
    exact (mul_le_mul_left hL).mp hh'
  have henergy : 256*(η*L*β^2)≤Δ := by
    have hh := mul_le_mul_of_nonneg_right hη1 (show 0≤256*L*β^2 by positivity)
    nlinarith only [hh,hβsq]
  have harg : 256≤Δ/(η*L*β^2) := (le_div_iff₀ (by positivity)).mpr henergy
  have harg0 : 0≤Δ/(η*L*β^2) := by positivity
  have hT : 256≤T := (Nat.le_floor_iff harg0).mpr (by exact_mod_cast harg)
  have hupper : (T:ℝ)*η*L*β^2≤Δ := by
    have hh := (Nat.floor_le harg0)
    have hh' := (le_div_iff₀ (show 0<η*L*β^2 by positivity)).mp hh
    change (T:ℝ)*(η*L*β^2)≤Δ at hh'
    nlinarith only [hh']
  have hlower : (η/(2048*A^4))*L*κ^2*Δ/ε^2≤(T:ℝ) := by
    have hh := LowerAlgebra.natFloor_half_lower (Δ/(η*L*β^2)) (by linarith only [harg])
    change (Δ/(η*L*β^2))/2≤(T:ℝ) at hh
    apply le_trans _ hh
    apply le_of_eq
    dsimp [β,innerWidth]
    field_simp
    ring
  have hIndex : T-1+1=T := by omega
  exact ⟨hβ,hβθ,hT,hIndex,hupper,hlower⟩

end Bilevel.MultiscaleMean
