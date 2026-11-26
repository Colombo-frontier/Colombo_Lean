import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

open scoped Topology ContDiff
open Filter Set

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual full Fréchet jet, including its value (order zero). -/
def SameJet (p : ℕ) (f g : E → ℝ) (x : E) : Prop :=
  ∀ r ≤ p, iteratedFDeriv ℝ r f x = iteratedFDeriv ℝ r g x

/-- Vanishing of the actual derivatives, not an abstract derivative placeholder. -/
def FlatAt (f : E → ℝ) (x : E) : Prop :=
  ∀ r : ℕ, iteratedFDeriv ℝ r f x = 0

private theorem nat_le_infty (r : ℕ) : (r : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)

theorem flatAt_of_iteratedDeriv_eq_zero {G : ℝ → ℝ} {s : ℝ}
    (h : ∀ r : ℕ, iteratedDeriv r G s = 0) : FlatAt G s := by
  intro r
  ext v
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, h]

/-- The flat-composition lemma also covers the boundary `u x = a`. -/
theorem flatAt_comp {G : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hG : ContDiff ℝ ∞ G) (hu : ContDiff ℝ ∞ u)
    (hflat : FlatAt G (u x)) : FlatAt (G ∘ u) x := by
  intro r
  rw [iteratedFDeriv_comp hG.contDiffAt hu.contDiffAt (nat_le_infty r)]
  change ∀ r, _ at hflat
  ext v
  simp [FormalMultilinearSeries.taylorComp,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, hflat]

theorem flat_gate_composition {G : ℝ → ℝ} {u : E → ℝ} {x : E} {a : ℝ}
    (hG : ContDiff ℝ ∞ G) (hu : ContDiff ℝ ∞ u)
    (hplateau : ∀ s ≤ a, ∀ r : ℕ, iteratedDeriv r G s = 0)
    (hx : u x ≤ a) : FlatAt (G ∘ u) x :=
  flatAt_comp hG hu (flatAt_of_iteratedDeriv_eq_zero (hplateau _ hx))

theorem flatAt_mul {f g : E → ℝ} {x : E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hflat : FlatAt f x) : FlatAt (fun y => f y * g y) x := by
  intro r
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := r) (nat_le_infty r)
  change ∀ r, _ at hflat
  simpa only [hflat, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] using h

theorem flatAt_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {x : E}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hflat : ∀ i ∈ s, FlatAt (f i) x) : FlatAt (fun y => ∑ i ∈ s, f i y) x := by
  intro r
  rw [iteratedFDeriv_sum (fun i hi => (hf i hi).of_le (nat_le_infty r))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hflat i hi r)

/-- Adding any finite family of closed smooth links leaves every jet unchanged. -/
theorem full_jet_opacity {ι : Type*} (s : Finset ι)
    {base : E → ℝ} {G : ℝ → ℝ} {u v : ι → E → ℝ} {x : E} {a : ℝ}
    (hbase : ContDiff ℝ ∞ base) (hG : ContDiff ℝ ∞ G)
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hv : ∀ i ∈ s, ContDiff ℝ ∞ (v i))
    (hplateau : ∀ t ≤ a, ∀ r : ℕ, iteratedDeriv r G t = 0)
    (hx : ∀ i ∈ s, u i x ≤ a) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y => base y + ∑ i ∈ s, G (u i y) * v i y) x =
      iteratedFDeriv ℝ r base x := by
  have hlink : ∀ i ∈ s, ContDiff ℝ ∞ (fun y => G (u i y) * v i y) :=
    fun i hi => (hG.comp (hu i hi)).mul (hv i hi)
  have hflat : FlatAt (fun y => ∑ i ∈ s, G (u i y) * v i y) x :=
    flatAt_sum s hlink (fun i hi =>
      flatAt_mul (hG.comp (hu i hi)) (hv i hi)
        (flat_gate_composition hG (hu i hi) hplateau (hx i hi)))
  rw [iteratedFDeriv_add_apply' (hbase.contDiffAt.of_le (nat_le_infty r))
    ((ContDiff.sum hlink).contDiffAt.of_le (nat_le_infty r)), hflat r, add_zero]

end FullJet
