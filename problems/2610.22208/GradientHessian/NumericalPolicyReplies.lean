import GradientHessian.NumericalOrdinaryProcedure
import GradientHessian.CensoredPolicyReplies

/-! Total chronological callbacks assembled from an independent external
factor and a supplied numerical table. The target matrix is absent; the
ordinary callback accepts its sole target-dependent input as a vector Ay. -/

noncomputable section
namespace GradientHessian.NumericalPolicyReplies
open Classical HigherHierarchy HierarchyParameters HierarchyAddresses CensoredHierarchy
  CensoredOracle ControllerCensor NumericalCachedOracle NumericalCoefficientPatch
  FrontierState TaskState

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

def ordinary (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Ay : EuclideanSpace ℝ (Fin d)) :
    ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) :=
  if hc : TaskState.current before=some leaf then
    ordinaryDecoder K t (planAt before after leaf hc t)
      ((cached P B fallback t ((leafEquiv t).symm leaf) w c,Z),Ay)
  else CensoredPolicy.ordinaryReply K t (cached P B fallback t ((leafEquiv t).symm leaf) w c) before after Z

def rich (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) :=
  CensoredPolicy.richReply K t (cached P B fallback t ((leafEquiv t).symm leaf) w c) before after Z

theorem ordinary_current {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell) (hc : TaskState.current before=some leaf)
    (hb : ∀ j,j≤(leafMask t (planAt before after leaf hc t)).current →
      c.1 j=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 j)
    (ha : ∀ j,j<(leafMask t (planAt before after leaf hc t)).current ∨
      (j=(leafMask t (planAt before after leaf hc t)).current ∧
        (leafMask t (planAt before after leaf hc t)).readout=true) →
      c.2 j=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 j)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Ay : EuclideanSpace ℝ (Fin d)) :
    ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z Ay=
      ordinaryDecoder K t (planAt before after leaf hc t) ((RawHierarchy.coefficients P B fallback t x,Z),Ay) := by
  rw [ordinary,dif_pos hc]
  have hb' := hb
  have ha' := ha
  rw [← selectedLeaf_plan before after leaf hc] at hb' ha'
  have hh := NumericalCachedOracle.ordinary_current P B fallback hK t (planAt before after leaf hc t) x c hb' ha' Z Ay
  simpa only [selectedLeaf_plan] using hh.symm

theorem rich_future {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (before after : State (t+1) (4096*J^2+1) ell) (cur : Leaf (t+1))
    (hc : TaskState.current before=some cur)
    (hf : FutureLeaf t (planAt before after cur hc t) ((leafEquiv t).symm leaf))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z=
      CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  unfold rich
  rw [CensoredPolicy.richReply_current _ _ _ _ _ cur hc,CensoredPolicy.richReply_current _ _ _ _ _ cur hc]
  exact (NumericalCachedOracle.rich_before_supply P B fallback hK t _ _ x c hf Z).symm

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]

theorem ordinary_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × EuclideanSpace ℝ (Fin d) =>
      ordinary P B fallback t leaf K q.1.1.1 q.1.1.2 before after q.1.2 q.2) := by
  have hcache : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × EuclideanSpace ℝ (Fin d) =>
      cached P B fallback t ((leafEquiv t).symm leaf) q.1.1.1 q.1.1.2) :=
    (cached_measurable P B fallback t ((leafEquiv t).symm leaf)).comp (measurable_fst.comp measurable_fst)
  by_cases hc : TaskState.current before=some leaf
  · simp only [ordinary,dif_pos hc]
    exact (ordinaryDecoder_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
      hK t (planAt before after leaf hc t)).measurable.comp
      ((hcache.prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  · simp only [ordinary,dif_neg hc]
    exact (CensoredPolicy.ordinaryReply_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
      hK t before after).measurable.comp (hcache.prodMk (measurable_snd.comp measurable_fst))

theorem rich_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      rich P B fallback t leaf K q.1.1 q.1.2 before after q.2) :=
  (CensoredPolicy.richReply_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
    hK t before after).measurable.comp
    (((cached_measurable P B fallback t ((leafEquiv t).symm leaf)).comp measurable_fst).prodMk measurable_snd)

end GradientHessian.NumericalPolicyReplies
