import GradientHessian.NumericalCachedOracle
import GradientHessian.OracleControl

/-! The cached full-physical ordinary decoder as one genuine ambient oracle
procedure. Its initial seed is only the external factor, supplied cache and
physical point; the target matrix enters through exactly one reply. -/

noncomputable section
namespace GradientHessian.NumericalOrdinaryProcedure
open Classical MeasureTheory LowRank OracleComposition HigherHierarchy HierarchyParameters
  CensoredHierarchy CensoredOracle NumericalCachedOracle NumericalCoefficientPatch

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]

def coordinates (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (p : Plan (4096*J^2) t)
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]

def decodeReply (K : ℝ)
    (q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × (Fin d → ℝ)) :
    ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) :=
  ordinaryDecoder K t p ((cached P B fallback t (selectedLeaf (4096*J^2) t p) q.1.1.1 q.1.1.2,
    q.1.2),(coordinates d).symm q.2)

theorem decodeReply_measurable {K : ℝ} (hK : 0<K) :
    Measurable (decodeReply (n := n) (E := E) (H := H) P B fallback t p K) := by
  have hcache : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × (Fin d → ℝ) =>
      cached P B fallback t (selectedLeaf (4096*J^2) t p) q.1.1.1 q.1.1.2) :=
    (cached_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t
      (selectedLeaf (4096*J^2) t p)).comp (measurable_fst.comp measurable_fst)
  have hmap : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × (Fin d → ℝ) =>
      ((cached P B fallback t (selectedLeaf (4096*J^2) t p) q.1.1.1 q.1.1.2,q.1.2),
        (coordinates d).symm q.2)) :=
    (hcache.prodMk (measurable_snd.comp measurable_fst)).prodMk
      ((coordinates d).symm.continuous.measurable.comp measurable_snd)
  exact (ordinaryDecoder_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) hK t p).measurable.comp hmap

def procedure {K : ℝ} (hK : 0<K) :
    Procedure d 1 ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)) where
  policy := (⟨fun q => coordinates d (numericalMap t q.2),
    (coordinates d).continuous.measurable.comp
      ((numericalMap (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t).continuous.measurable.comp
        measurable_snd)⟩,PUnit.unit)
  decode := ⟨decodeReply (n := n) P B fallback t p K,decodeReply_measurable (n := n) P B fallback t p hK⟩

theorem run_procedure {K : ℝ} (hK : 0<K) (A : Matrix (Fin d) (Fin d) ℝ)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    (procedure P B fallback t p hK).run A ((w,c),Z)=
      ordinaryDecoder K t p ((cached P B fallback t (selectedLeaf (4096*J^2) t p) w c,Z),
        matrixEuclideanMap A (numericalMap t Z)) := by
  rfl

theorem calls_procedure {K : ℝ} (hK : 0<K) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    ((procedure P B fallback t p hK).toProgram ((w,c),Z)).calls oracle=1 :=
  Procedure.calls_toProgram _ oracle _

theorem source_reply_exact {K : ℝ} (hK : 0<K) (A : Matrix (Fin d) (Fin d) ℝ)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (hb : ∀ j,j≤(leafMask t p).current →
      c.1 j=(atLeaf t (selectedLeaf (4096*J^2) t p) (RawHierarchy.coefficients P B fallback t x)).2.1 j)
    (ha : ∀ j,j<(leafMask t p).current ∨ (j=(leafMask t p).current ∧ (leafMask t p).readout=true) →
      c.2 j=(atLeaf t (selectedLeaf (4096*J^2) t p) (RawHierarchy.coefficients P B fallback t x)).2.2.1 j)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    (procedure P B fallback t p hK).run A
      (((RawLeafFactor.factor t (selectedLeaf (4096*J^2) t p) x).2,c),Z)=
      ordinaryDecoder K t p ((RawHierarchy.coefficients P B fallback t x,Z),matrixEuclideanMap A (numericalMap t Z)) := by
  rw [run_procedure]
  exact (ordinary_current P B fallback hK t p x c hb ha Z _).symm

end GradientHessian.NumericalOrdinaryProcedure
