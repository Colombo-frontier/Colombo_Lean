import NCBall.ShadowCoupling
import NCBall.TransverseMeasurement

/-! # Measurability of the actual finite-sum shadow responses -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace NCBall

variable {A : Type*} [MeasurableSpace A] {n : ℕ}

theorem roomCenter_measurable_data (ρ : ℝ) (U : A → ℕ → Space n)
    (hU : ∀ k, Measurable (fun a => U a k)) (j : ℕ) :
    Measurable (fun a => roomCenter ρ (U a) j) := by
  unfold roomCenter
  fun_prop

theorem localBump_measurable_data (v y : A → Space n) (hv : Measurable v) (hy : Measurable y) :
    Measurable (fun a => localBump (v a) (y a)) := by
  exact (((cutoff_smooth n).continuous.measurable).comp hy).mul (hv.inner hy)

theorem terminalBump_measurable_data (y : A → Space n) (hy : Measurable y) :
    Measurable (fun a => terminalBump (y a)) :=
  (terminalBump_smooth n).continuous.measurable.comp hy

theorem shadowValue_measurable_data (M : ℕ) (ρ γ lam : ℝ) (r : A → ℕ)
    (c V : A → ℕ → Space n) (x : A → Space n)
    (hr : Measurable r) (hc : ∀ k, Measurable (fun a => c a k))
    (hV : ∀ k, Measurable (fun a => V a k)) (hx : Measurable x) :
    Measurable (fun a => shadowValue M (r a) ρ γ lam (c a) (V a) (x a)) := by
  have hb (k : ℕ) : Measurable (fun a => localBump (V a k) (ρ⁻¹ • (x a - c a k))) :=
    localBump_measurable_data _ _ (hV k) ((hx.sub (hc k)).const_smul ρ⁻¹)
  have hs : Measurable (fun a => ∑ k ∈ Finset.range M,
      if k ≤ r a then localBump (V a k) (ρ⁻¹ • (x a - c a k)) else 0) := by
    apply Finset.measurable_sum
    intro k _
    exact Measurable.ite (measurableSet_le measurable_const hr) (hb k) measurable_const
  have ht := terminalBump_measurable_data (fun a => ρ⁻¹ • (x a - c a M))
    ((hx.sub (hc M)).const_smul ρ⁻¹)
  have hclock : Measurable (fun a => x a 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).measurable.comp hx
  exact (hclock.const_mul (-γ) |>.add (hs.const_mul (lam * ρ))).add
    (Measurable.ite (measurableSet_le measurable_const hr) (ht.const_mul (γ * ρ)) measurable_const)

theorem shadowPastValue_measurable_data (j : ℕ) (ρ γ lam : ℝ)
    (c V : A → ℕ → Space n) (x : A → Space n)
    (hc : ∀ k, Measurable (fun a => c a k))
    (hV : ∀ k, Measurable (fun a => V a k)) (hx : Measurable x) :
    Measurable (fun a => shadowPastValue j ρ γ lam (c a) (V a) (x a)) := by
  have hs : Measurable (fun a => ∑ k ∈ Finset.range j,
      localBump (V a k) (ρ⁻¹ • (x a - c a k))) := by
    apply Finset.measurable_sum
    intro k _
    exact localBump_measurable_data _ _ (hV k) ((hx.sub (hc k)).const_smul ρ⁻¹)
  have hclock : Measurable (fun a => x a 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).measurable.comp hx
  exact hclock.const_mul (-γ) |>.add (hs.const_mul (lam * ρ))

end NCBall
