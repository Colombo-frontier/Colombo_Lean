import Bilevel.PolishedProjectionDimension
import Bilevel.RawGenieBorelProbability

/-! Source two-frame projection certificate. There is one S-column macro
Haar frame and one (S*M)-column micro Haar frame, in possibly different
ambient dimensions. The whole other frame and private randomness may be
frozen as independent context for either selected-frame policy. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.PolishedTwoFrameProjection
open EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel
open PolishedProjectionDimension

theorem safe_mono {d T m r : ℕ} {a b : ℝ} (hab : a≤b)
    (P : RawGenieProtocol.Protocol d T m r)
    (W : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T) :
    RawGenieProtocol.Safe a P W S U → RawGenieProtocol.Safe b P W S U := by
  have hm : ∀ W S, GenieProtocol.BoundedEnergy W S U a →
      GenieProtocol.BoundedEnergy W S U b := fun _ _ h i hi => (h i hi).trans hab
  induction P generalizing W S with
  | halt => exact hm W S
  | query q next ih => exact fun h => ⟨hm _ _ h.1,ih _ _ _ h.2⟩
  | reveal i next ih => exact fun h => ⟨hm _ _ h.1,ih _ _ _ h.2⟩

theorem raw_explicit_dimension {d K m : ℕ} {H : Memory.{u}}
    (P : Policy d K H m K) {C : Type*} [MeasurableSpace C]
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (R τ δ : ℝ) (hm : 0<m) (hK : 0<K) (hR : 0<R) (hτ : 0<τ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hd : sourceDimension m K R τ δ≤d) :
    ∃ hKd : K≤d,
      (ρ.prod (HaarFrame.frameLaw d K hKd)) {p | ¬RawGenieProtocol.Safe
        (τ^2/(4*R^2)) (compile P (initial p.1)) ⊥ ∅ p.2}≤ENNReal.ofReal (δ/8) := by
  obtain ⟨n,b,hKd,hdim,_,hb,hb2,hcap,henergy,hprob⟩ :=
    explicit_dimension_sufficient m K d R τ δ hm hK hR hτ hδ hδ1 hd
  refine ⟨hKd,?_⟩
  have hp := randomized_unsafe_probability hKd P initial hi ρ b hb hb2 hdim hcap
  have he := (GenieProtocol.envelope_twice m K b hb.le hcap).trans henergy
  have hs : {p : C × Frame d K | ¬RawGenieProtocol.Safe
      (τ^2/(4*R^2)) (compile P (initial p.1)) ⊥ ∅ p.2} ⊆
      {p | ¬RawGenieProtocol.Safe (ProjectionEnergy.envelope ((m:ℝ)*b) K)
        (compile P (initial p.1)) ⊥ ∅ p.2} :=
    fun _ h h' => h (safe_mono he _ _ _ _ h')
  exact ((measure_mono hs).trans hp).trans_eq hprob

def macroExpose {C A B : Type*} (p : C × (A × B)) : (C × B) × A :=
  ((p.1,p.2.2),p.2.1)

theorem macroExpose_preserving {C A B : Type*}
    [MeasurableSpace C] [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure C) (μ : Measure A) (ν : Measure B)
    [SFinite ρ] [SFinite μ] [SFinite ν] :
    MeasurePreserving (macroExpose (C:=C) (A:=A) (B:=B))
      (ρ.prod (μ.prod ν)) ((ρ.prod ν).prod μ) := by
  have hs := (MeasurePreserving.id ρ).prod (Measure.measurePreserving_swap (μ:=μ) (ν:=ν))
  have ha := (measurePreserving_prodAssoc ρ ν μ).symm
    (MeasurableEquiv.prodAssoc : (C × B) × A ≃ᵐ C × (B × A))
  exact ha.comp hs

def microExpose {C A B : Type*} (p : C × (A × B)) : (C × A) × B :=
  ((p.1,p.2.1),p.2.2)

theorem microExpose_preserving {C A B : Type*}
    [MeasurableSpace C] [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure C) (μ : Measure A) (ν : Measure B)
    [SFinite ρ] [SFinite μ] [SFinite ν] :
    MeasurePreserving (microExpose (C:=C) (A:=A) (B:=B))
      (ρ.prod (μ.prod ν)) ((ρ.prod μ).prod ν) :=
  (measurePreserving_prodAssoc ρ μ ν).symm
    (MeasurableEquiv.prodAssoc : (C × A) × B ≃ᵐ C × (A × B))

theorem source_two_frame_projection {dx du S M N : ℕ}
    {Hx : Memory.{u}} {Hu : Memory.{v}} {C : Type*} [MeasurableSpace C]
    (ρ : Measure C) [IsProbabilityMeasure ρ]
    (Px : Policy dx S Hx (N+1) S) (Pu : Policy du (S*M) Hu (2*N+1) (S*M))
    (ix : C × Frame du (S*M) → Hx) (hix : Measurable ix)
    (iu : C × Frame dx S → Hu) (hiu : Measurable iu)
    (Rx Ru τx τu δ : ℝ) (hS : 0<S) (hM : 0<M)
    (hRx : 0<Rx) (hRu : 0<Ru) (hτx : 0<τx) (hτu : 0<τu)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hdx : sourceDimension (N+1) S Rx τx δ≤dx)
    (hdu : sourceDimension (2*N+1) (S*M) Ru τu δ≤du) :
    ∃ hx : S≤dx, ∃ hu : S*M≤du,
      (ρ.prod ((HaarFrame.frameLaw dx S hx).prod (HaarFrame.frameLaw du (S*M) hu)))
        {p | ¬RawGenieProtocol.Safe (τx^2/(4*Rx^2)) (compile Px (ix (p.1,p.2.2))) ⊥ ∅ p.2.1 ∨
          ¬RawGenieProtocol.Safe (τu^2/(4*Ru^2)) (compile Pu (iu (p.1,p.2.1))) ⊥ ∅ p.2.2}≤
        ENNReal.ofReal δ := by
  obtain ⟨_,_,hx,_,_,_,_,_,_,_⟩ := explicit_dimension_sufficient (N+1) S dx Rx τx δ
    (by omega) hS hRx hτx hδ hδ1 hdx
  obtain ⟨_,_,hu,_,_,_,_,_,_,_⟩ := explicit_dimension_sufficient (2*N+1) (S*M) du Ru τu δ
    (by omega) (Nat.mul_pos hS hM) hRu hτu hδ hδ1 hdu
  let μx := HaarFrame.frameLaw dx S hx
  let μu := HaarFrame.frameLaw du (S*M) hu
  let μ := ρ.prod (μx.prod μu)
  let Bx : Set ((C × Frame du (S*M)) × Frame dx S) :=
    {p | ¬RawGenieProtocol.Safe (τx^2/(4*Rx^2)) (compile Px (ix p.1)) ⊥ ∅ p.2}
  let Bu : Set ((C × Frame dx S) × Frame du (S*M)) :=
    {p | ¬RawGenieProtocol.Safe (τu^2/(4*Ru^2)) (compile Pu (iu p.1)) ⊥ ∅ p.2}
  have hBx : MeasurableSet Bx :=
    (hix.prodMap measurable_id) (initial_unsafe_measurable Px _)
  have hBu : MeasurableSet Bu :=
    (hiu.prodMap measurable_id) (initial_unsafe_measurable Pu _)
  obtain ⟨_,hpx⟩ := raw_explicit_dimension Px ix hix (ρ.prod μu)
    Rx τx δ (by omega) hS hRx hτx hδ hδ1 hdx
  obtain ⟨_,hpu⟩ := raw_explicit_dimension Pu iu hiu (ρ.prod μx)
    Ru τu δ (by omega) (Nat.mul_pos hS hM) hRu hτu hδ hδ1 hdu
  have hxbound : μ (macroExpose ⁻¹' Bx)≤ENNReal.ofReal (δ/8) := by
    rw [(macroExpose_preserving ρ μx μu).measure_preimage hBx.nullMeasurableSet]
    exact hpx
  have hubound : μ (microExpose ⁻¹' Bu)≤ENNReal.ofReal (δ/8) := by
    rw [(microExpose_preserving ρ μx μu).measure_preimage hBu.nullMeasurableSet]
    exact hpu
  refine ⟨hx,hu,?_⟩
  change μ ((macroExpose ⁻¹' Bx) ∪ (microExpose ⁻¹' Bu))≤ENNReal.ofReal δ
  calc
    _ ≤ μ (macroExpose ⁻¹' Bx)+μ (microExpose ⁻¹' Bu) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ/8)+ENNReal.ofReal (δ/8) := add_le_add hxbound hubound
    _ ≤ ENNReal.ofReal δ := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)

end Bilevel.PolishedTwoFrameProjection
