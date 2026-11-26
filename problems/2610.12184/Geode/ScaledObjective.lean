import Geode.CarrierOracle

/-! Positive rescaling of actual hyperbolic objectives and their ordinary
first-order oracles. The carrier instances below satisfy `AdmissibleObjective`
in the actual oracle model, including their global minimizer. -/

namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scaledObjective (a : ℝ) (f : Point E → ℝ) : Point E → ℝ := fun x => a * f x

def scaledOracle (a : ℝ) (O : Point E → FirstOrderReply E) :
    Point E → FirstOrderReply E := fun x => (a * (O x).1, a • (O x).2)

theorem GConvexFunction.const_mul {f : Point E → ℝ} (hf : GConvexFunction f)
    {a : ℝ} (ha : 0 ≤ a) : GConvexFunction (scaledObjective a f) := by
  intro x y t ht ht1
  have h := mul_le_mul_of_nonneg_left (hf x y t ht ht1) ha
  dsimp only [scaledObjective]
  nlinarith

theorem scaledObjective_lipschitz {f : Point E → ℝ} {a L : ℝ}
    (ha : 0 ≤ a) (hf : ∀ x y, |f x - f y| ≤ L * dist x y) :
    ∀ x y, |scaledObjective a f x - scaledObjective a f y| ≤
      (a * L) * dist x y := by
  intro x y
  dsimp only [scaledObjective]
  rw [← mul_sub, abs_mul, abs_of_nonneg ha, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x y) ha

theorem scaledObjective_minimizer_iff {f : Point E → ℝ} {a : ℝ}
    (ha : 0 < a) (p : Point E) :
    (∀ y, scaledObjective a f p ≤ scaledObjective a f y) ↔ ∀ y, f p ≤ f y := by
  simp only [scaledObjective, mul_le_mul_left ha]

theorem scaledObjective_unique_minimizer {f : Point E → ℝ} {a : ℝ}
    (ha : 0 < a) {p : Point E}
    (hf : ∀ x, (∀ y, f x ≤ f y) ↔ x = p) :
    ∀ x, (∀ y, scaledObjective a f x ≤ scaledObjective a f y) ↔ x = p := by
  intro x
  exact (scaledObjective_minimizer_iff ha x).trans (hf x)

theorem scaledObjective_isSubgradient {f : Point E → ℝ} {x : Point E}
    {g : Ambient E} {a : ℝ} (ha : 0 ≤ a) (hg : IsSubgradient f x g) :
    IsSubgradient (scaledObjective a f) x (a • g) := hg.const_mul ha

theorem LegalOracle.const_mul {f : Point E → ℝ} {O : Point E → FirstOrderReply E}
    (hO : LegalOracle f O) {a : ℝ} (ha : 0 ≤ a) :
    LegalOracle (scaledObjective a f) (scaledOracle a O) := by
  intro x
  exact ⟨congrArg (fun v : ℝ => a * v) (hO x).1, (hO x).2.const_mul ha⟩

theorem AdmissibleObjective.const_mul {o : Point E} {R L a : ℝ}
    {f : Point E → ℝ} (hf : AdmissibleObjective o R L f) (ha : 0 ≤ a) :
    AdmissibleObjective o R (a * L) (scaledObjective a f) := by
  refine ⟨hf.convex.const_mul ha, scaledObjective_lipschitz ha hf.lipschitz, ?_⟩
  obtain ⟨p, hp, hmin⟩ := hf.minimizer
  exact ⟨p, hp, fun y => mul_le_mul_of_nonneg_left (hmin y) ha⟩

theorem carrier_admissible {o p : Point E} {R μ : ℝ} {K : Set (Point E)}
    (hK : IsCompact K) (hKg : GConvex K) (hp : p ∈ K) (hR : dist o p ≤ R)
    (hμ : 0 < μ) (hμ1 : μ < 1) :
    AdmissibleObjective o R 1 (Geode.carrierValue K p μ) := by
  obtain ⟨hc, hl, _, _, hmin, _⟩ := metric_carrier hK hKg hp hμ hμ1
  refine ⟨hc, ?_, p, hR, (hmin p).mpr rfl⟩
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one] using hl.dist_le_mul x y

theorem scaled_carrier_admissible {o p : Point E} {R L μ : ℝ} {K : Set (Point E)}
    (hK : IsCompact K) (hKg : GConvex K) (hp : p ∈ K) (hR : dist o p ≤ R)
    (hL : 0 ≤ L) (hμ : 0 < μ) (hμ1 : μ < 1) :
    AdmissibleObjective o R L (scaledObjective L (Geode.carrierValue K p μ)) := by
  simpa only [mul_one] using (carrier_admissible hK hKg hp hR hμ hμ1).const_mul hL

theorem scaled_carrierOracle_legal {p : Point E} {L μ : ℝ} {K : Set (Point E)}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    LegalOracle (scaledObjective L (Geode.carrierValue K p μ))
      (scaledOracle L (carrierOracle (p := p) hK hKg hne hμ hμ1)) :=
  (carrierOracle_legal hK hKg hne hμ hμ1).const_mul hL

theorem scaled_carrier_unique_minimizer {p : Point E} {L μ : ℝ} {K : Set (Point E)}
    (hp : p ∈ K) (hL : 0 < L) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∀ x, (∀ y, scaledObjective L (Geode.carrierValue K p μ) x ≤
      scaledObjective L (Geode.carrierValue K p μ) y) ↔ x = p :=
  scaledObjective_unique_minimizer hL
    (fun _ => Geode.carrierValue_unique_minimizer hp hμ hμ1)

theorem scaled_carrier_floor {p y : Point E} {L μ : ℝ} {K : Set (Point E)}
    (hne : K.Nonempty) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    L * μ * dist y p ≤ scaledObjective L (Geode.carrierValue K p μ) y := by
  simpa only [scaledObjective, mul_assoc] using
    mul_le_mul_of_nonneg_left (Geode.carrierValue_floor (p := p) (y := y) hne hμ hμ1) hL

@[simp] theorem scaled_carrier_at_center {p : Point E} {L μ : ℝ} {K : Set (Point E)}
    (hp : p ∈ K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    scaledObjective L (Geode.carrierValue K p μ) p = 0 := by
  simp only [scaledObjective, Geode.carrierValue_at_center hp hμ hμ1, mul_zero]

end Geode.Lorentz
