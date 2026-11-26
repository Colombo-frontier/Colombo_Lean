import GradientHessian.NumericalCoefficientPatch

/-! A source numerical cache assembled without the target matrix or marks.
Its coordinates are the original external raw factor and the explicitly
supplied forcing/readout table. The ordinary oracle then uses exactly Ay. -/

noncomputable section
namespace GradientHessian.NumericalCachedOracle
open Classical HigherHierarchy HierarchyParameters CensoredHierarchy CensoredOracle
  RawHierarchy NumericalCoefficientPatch

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

abbrev Cache (d J : ℕ) := (Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin d)) ×
  (Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin d))

def restore (t : ℕ) (i : LeafSlot t) (w : RawLeafFactor.Rest d n r J E H t) : Raw d n r J E H t :=
  (RawLeafFactor.factor t i).symm ((0,0),w)

def cached (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) :
    Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t :=
  patch t i (0,c) (coefficients P B fallback t (restore t i w))

theorem restore_measurable (t : ℕ) (i : LeafSlot t) :
    Measurable (restore (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i) :=
  (RawLeafFactor.factor t i).symm.measurable.comp (measurable_const.prodMk measurable_id)

theorem cached_eq_patch (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (x : Raw d n r J E H t) (c : Cache d J) :
    cached P B fallback t i (RawLeafFactor.factor t i x).2 c=
      patch t i (0,c) (coefficients P B fallback t x) := by
  apply patch_coefficients_rest P B fallback t i
  have he := congrArg (fun z : RawFirstFactor.Target d n r J × RawLeafFactor.Rest d n r J E H t => z.2)
    ((RawLeafFactor.factor t i).apply_symm_apply ((0,0),(RawLeafFactor.factor t i x).2))
  exact he

/-- Before this leaf becomes current, even its entire numerical table may
be replaced. Both the rich reply and the selected matrix stay identical. -/
theorem rich_before_supply (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan (4096*J^2) t)
    (i : LeafSlot t) (x : Raw d n r J E H t) (c : Cache d J) (hf : FutureLeaf t p i)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    richDecoder K t p (coefficients P B fallback t x,Z)=
      richDecoder K t p (cached P B fallback t i (RawLeafFactor.factor t i x).2 c,Z) := by
  rw [cached_eq_patch]
  exact rich_future_patch hK t p i _ _ hf Z

/-- Every matrix-independent part of the current ordinary reply is supplied
by the external factor and the finite table. Its only additional input is Ay. -/
theorem ordinary_current (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan (4096*J^2) t)
    (x : Raw d n r J E H t) (c : Cache d J)
    (hb : ∀ j,j≤(leafMask t p).current →
      c.1 j=(atLeaf t (selectedLeaf (4096*J^2) t p) (coefficients P B fallback t x)).2.1 j)
    (ha : ∀ j,j<(leafMask t p).current ∨ (j=(leafMask t p).current ∧ (leafMask t p).readout=true) →
      c.2 j=(atLeaf t (selectedLeaf (4096*J^2) t p) (coefficients P B fallback t x)).2.2.1 j)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Ay : EuclideanSpace ℝ (Fin d)) :
    ordinaryDecoder K t p ((coefficients P B fallback t x,Z),Ay)=
      ordinaryDecoder K t p ((cached P B fallback t (selectedLeaf (4096*J^2) t p)
        (RawLeafFactor.factor t (selectedLeaf (4096*J^2) t p) x).2 c,Z),Ay) := by
  rw [cached_eq_patch]
  exact ordinary_selected_patch hK t p _ (0,c) hb ha Z Ay

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]

theorem cached_measurable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) :
    Measurable (fun q : RawLeafFactor.Rest d n r J E H t × Cache d J =>
      cached P B fallback t i q.1 q.2) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := borel _
  letI : BorelSpace (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hθ : Measurable (fun q : RawLeafFactor.Rest d n r J E H t × Cache d J =>
      coefficients P B fallback t (restore t i q.1)) :=
    (coefficients_measurable P B fallback t).comp ((restore_measurable t i).comp measurable_fst)
  haveI := HierarchyParameters.parameterBorel (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t
  haveI : BorelSpace (numerical (Y := EuclideanSpace ℝ (Fin d)) (m := 4096*J^2) t) := by
    change BorelSpace ((EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) × Cache d J)
    infer_instance
  have hp : Measurable (fun q : numerical (Y := EuclideanSpace ℝ (Fin d)) (m := 4096*J^2) t ×
      Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => patch t i q.1 q.2) :=
    (patch_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t i).measurable
  exact hp.comp ((measurable_const.prodMk measurable_snd).prodMk hθ)

end GradientHessian.NumericalCachedOracle
