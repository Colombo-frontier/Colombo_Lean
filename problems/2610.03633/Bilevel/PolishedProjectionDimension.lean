import Bilevel.GenieTheorem
import Bilevel.OrdinaryFrameObserver

/-! Numerical sufficiency of the explicit logarithmic dimension expression
in hier:eq:dimension, for the finite Haar projection/revelation protocol.
The protocol itself and the two-frame source translation are separate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedProjectionDimension
universe u
set_option maxHeartbeats 1200000

def sourceDimension (m K : ℕ) (R τ δ : ℝ) : ℝ :=
  128*((m:ℝ)+K+2+(m:ℝ)*((K:ℝ)+R^2/τ^2)*Real.log (16*(m:ℝ)*K/δ))

theorem explicit_dimension_sufficient (m K d : ℕ) (R τ δ : ℝ)
    (hm : 0<m) (hK : 0<K) (hR : 0<R) (hτ : 0<τ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hd : sourceDimension m K R τ δ≤d) :
    ∃ n : ℕ, ∃ b : ℝ, K≤d ∧ m+K+(n+1)≤d ∧ 0<n ∧ 0<b ∧ b≤2 ∧
      (K:ℝ)*((m:ℝ)*b)≤1/2 ∧ 2*(m:ℝ)*b≤τ^2/(4*R^2) ∧
      (m:ℝ≥0∞)*GenieProtocol.failurePerQuery K n b=ENNReal.ofReal (δ/8) := by
  have hm0 : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have hK0 : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hK1 : (1:ℝ)≤K := by exact_mod_cast hK
  have harg : 1<16*(m:ℝ)*K/δ := (lt_div_iff₀ hδ).mpr (by nlinarith)
  let l := Real.log (16*(m:ℝ)*K/δ)
  have hl : 0<l := Real.log_pos harg
  let base : ℝ := (m:ℝ)+K+2
  let scale : ℝ := (m:ℝ)*((K:ℝ)+R^2/τ^2)*l
  have hb0 : 0<base := by dsimp [base]; positivity
  have hs0 : 0≤scale := by dsimp [scale]; positivity
  have hd' : 128*(base+scale)≤(d:ℝ) := hd
  have hbase : m+K+2≤d := by
    have hb : base≤(d:ℝ) := by nlinarith
    dsimp [base] at hb
    exact_mod_cast hb
  let n := d-(m+K+2)
  have hneq : (n:ℝ)=(d:ℝ)-base := by
    dsimp [n,base]
    rw [Nat.cast_sub hbase]
    push_cast
    ring
  have hscale : 128*scale≤(n:ℝ) := by rw [hneq]; nlinarith
  have hscaleK : (m:ℝ)*K*l≤scale := by
    dsimp [scale]
    have hz : 0≤(m:ℝ)*(R^2/τ^2)*l := by positivity
    nlinarith
  have hscaleR : (m:ℝ)*(R^2/τ^2)*l≤scale := by
    dsimp [scale]
    have hz : 0≤(m:ℝ)*K*l := by positivity
    nlinarith
  have hn0 : 0<(n:ℝ) := by nlinarith [mul_pos (mul_pos hm0 hK0) hl]
  have hn : 0<n := Nat.cast_pos.mp hn0
  let b := 8*l/(n:ℝ)
  have hb : 0<b := by dsimp [b]; positivity
  have hbn : b*(n:ℝ)=8*l := by dsimp [b]; field_simp
  have hb2 : b≤2 := by
    dsimp [b]
    apply (div_le_iff₀ hn0).mpr
    have hmk : 1≤(m:ℝ)*K := by nlinarith
    nlinarith
  have hcap : (K:ℝ)*((m:ℝ)*b)≤1/2 := by
    apply (mul_le_mul_right hn0).mp
    nlinarith [show (K:ℝ)*((m:ℝ)*b)*(n:ℝ)=8*(m:ℝ)*K*l by rw [mul_assoc,mul_assoc,hbn];ring]
  have henergy : 2*(m:ℝ)*b≤τ^2/(4*R^2) := by
    apply (le_div_iff₀ (by positivity : 0<4*R^2)).mpr
    apply (mul_le_mul_right hn0).mp
    have he : (2*(m:ℝ)*b*(4*R^2))*(n:ℝ)=64*(m:ℝ)*R^2*l := by
      calc
        _ = 8*(m:ℝ)*R^2*(b*(n:ℝ)) := by ring
        _ = _ := by rw [hbn];ring
    have hs := mul_le_mul_of_nonneg_right (hscaleR.trans (by linarith : scale≤(n:ℝ)/128)) (sq_nonneg τ)
    have hc : (m:ℝ)*(R^2/τ^2)*l*τ^2=(m:ℝ)*R^2*l := by field_simp
    rw [hc] at hs
    rw [he]
    nlinarith
  have hbeq : b=GenieProtocol.logarithmicIncrement m K n (δ/4) := by
    unfold GenieProtocol.logarithmicIncrement
    dsimp [b,l]
    congr 2
    congr 1
    field_simp
    ring
  refine ⟨n,b,by omega,by dsimp [n];omega,hn,hb,hb2,hcap,henergy,?_⟩
  rw [hbeq,GenieProtocol.failurePerQuery,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  apply congrArg ENNReal.ofReal
  have hi := GenieProtocol.logarithmic_failure_identity m K n hm hK hn (δ/4) (by positivity)
  exact hi.trans (by ring)

theorem safe_mono {d K m r : ℕ} {a b : ℝ} (hab : a≤b)
    (P : GenieProtocol.Protocol d K m r)
    (W : Submodule ℝ (EuclideanGaussian.Space d)) (S : Set (Fin K))
    (U : ProjectionPosterior.Frame d K) :
    GenieProtocol.Safe a P W S U → GenieProtocol.Safe b P W S U := by
  induction P generalizing W S with
  | halt => exact fun h i hi => (h i hi).trans hab
  | query w next ih => exact fun h => ⟨fun i hi => (h.1 i hi).trans hab, ih _ _ _ h.2⟩
  | reveal i next ih => exact fun h => ⟨fun j hj => (h.1 j hj).trans hab, ih _ _ _ h.2⟩

/-- The literal logarithmic dimension bound controls every intermediate
projection, including the terminal insertions counted in `m`. -/
theorem single_frame_uniform_projection (m K d : ℕ) (R τ δ : ℝ)
    (hm : 0<m) (hK : 0<K) (hR : 0<R) (hτ : 0<τ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hd : sourceDimension m K R τ δ≤d) :
    ∃ n : ℕ, ∃ b : ℝ, ∃ hKd : K≤d, 0<n ∧ m+K+(n+1)≤d ∧
      ∀ P : GenieProtocol.Protocol d K m K, GenieProtocol.Regular b P →
        GenieProtocol.Valid P ⊥ →
        (HaarFrame.frameLaw d K hKd)
          {U | ¬GenieProtocol.Safe (τ^2/(4*R^2)) P ⊥ ∅ U}≤ENNReal.ofReal (δ/8) := by
  obtain ⟨n,b,hKd,hdim,hn,hb,hb2,hcap,hen,hprob⟩ :=
    explicit_dimension_sufficient m K d R τ δ hm hK hR hτ hδ hδ1 hd
  refine ⟨n,b,hKd,hn,hdim,?_⟩
  intro P hP hV
  have hs := GenieProtocol.unsafe_probability d K m K n hKd P b hb hb2 hdim hcap hP hV
  have he := (GenieProtocol.envelope_twice m K b hb.le hcap).trans hen
  have hsub : {U | ¬GenieProtocol.Safe (τ^2/(4*R^2)) P ⊥ ∅ U} ⊆
      {U | ¬GenieProtocol.Safe (ProjectionEnergy.envelope ((m:ℝ)*b) K) P ⊥ ∅ U} :=
    fun U h h' => h (safe_mono he P ⊥ ∅ U h')
  exact ((measure_mono hsub).trans hs).trans_eq hprob

/-- Original-query observer version: arbitrary Borel memory, two raw query
directions before each coin/revelation, and an arbitrary terminal output.
The numerical condition is exactly `hier:eq:dimension` with `m=2Q+1`. -/
theorem actual_observer_explicit_dimension {d K Q : ℕ}
    {H : TransportControllerMachine.Memory.{u}} {C : Type} [MeasurableSpace C]
    (L : OrdinaryFrame.Rules H d K) (initial : C → H) (hi : Measurable initial)
    (ρ : Measure C) [IsProbabilityMeasure ρ] (t : ℕ) (R τ δ : ℝ)
    (hK : 0<K) (hR : 0<R) (hτ : 0<τ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hd : sourceDimension (2*Q+1) K R τ δ≤d) :
    ∃ hKd : K≤d,
      (ρ.prod (HaarFrame.frameLaw d K hKd))
        {p | ¬OrdinaryFrame.Observed L (τ^2/(4*R^2)) Q K t
          (initial p.1,(⊥,∅)) p.2}≤ENNReal.ofReal (δ/8) := by
  obtain ⟨n,b,hKd,hdim,hn,hb,hb2,hcap,hen,hprob⟩ :=
    explicit_dimension_sufficient (2*Q+1) K d R τ δ (by omega) hK hR hτ hδ hδ1 hd
  refine ⟨hKd,?_⟩
  have hs := OrdinaryFrame.actual_observer hKd L initial hi ρ t b hb hb2 hdim hcap
  have hsub : {p : C × ProjectionPosterior.Frame d K |
      ¬OrdinaryFrame.Observed L (τ^2/(4*R^2)) Q K t (initial p.1,(⊥,∅)) p.2} ⊆
      {p | ¬OrdinaryFrame.Observed L (2*((2*Q+1:ℕ):ℝ)*b) Q K t
        (initial p.1,(⊥,∅)) p.2} :=
    fun p h h' => h (OrdinaryFrame.observed_mono L hen Q K t _ _ h')
  exact ((measure_mono hsub).trans hs).trans_eq hprob

end Bilevel.PolishedProjectionDimension
