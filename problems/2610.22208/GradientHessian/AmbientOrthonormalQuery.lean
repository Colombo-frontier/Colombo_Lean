import GradientHessian.DeferredGaussianChronological
import LowRank.GaussianAmbientTranscript

/-! Normalizing a unit ambient query orthogonal to all exposed columns
preserves that query exactly, including its physical coordinates. -/

noncomputable section
namespace GradientHessian.AmbientOrthonormal
open Classical Matrix MeasureTheory ProbabilityTheory LowRank DeferredGaussian
open scoped Matrix BigOperators InnerProductSpace

theorem orthogonal_coordinates_dot {d q r : ℕ} (B : Matrix (Fin d) (Fin q ⊕ Fin r) ℝ)
    (hB : B*Bᵀ=1) (v : Fin d → ℝ) :
    (Bᵀ *ᵥ v) ⬝ᵥ (Bᵀ *ᵥ v)=v ⬝ᵥ v := by
  rw [dotProduct_mulVec,vecMul_transpose,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]

theorem head_zero {d q r : ℕ} (vis : VisibleFactorData d q r) (v : Fin d → ℝ)
    (h : ∀ u∈queryColumns vis,v ⬝ᵥ u=0) : headQueryCoordinates vis v=0 := by
  funext i
  have hi : (fun k => vis.2 k (Sum.inl i))∈queryColumns vis := List.mem_ofFn.mpr ⟨i,rfl⟩
  simpa only [headQueryCoordinates,Matrix.mulVec,Matrix.transpose_apply,Pi.zero_apply,
    dotProduct_comm] using h _ hi

theorem tail_unit {d q r : ℕ} (vis : VisibleFactorData d q r) (v : Fin d → ℝ)
    (hB : vis.2*vis.2ᵀ=1) (hv : v ⬝ᵥ v=1) (hh : headQueryCoordinates vis v=0) :
    tailQueryCoordinates vis v ⬝ᵥ tailQueryCoordinates vis v=1 := by
  have he : vis.2ᵀ *ᵥ v=Sum.elim (headQueryCoordinates vis v) (tailQueryCoordinates vis v) := by
    funext i
    cases i <;> rfl
  have hd := orthogonal_coordinates_dot vis.2 hB v
  rw [he,sumElim_dotProduct_sumElim,hh,zero_dotProduct,zero_add,hv] at hd
  exact hd

theorem coordinate_norm_of_dot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r : ℕ}
    (b : OrthonormalBasis (Fin r) ℝ E) (v : Fin r → ℝ) (hv : v ⬝ᵥ v=1) :
    ‖(basisCoordinates b).symm v‖=1 := by
  have h := basisCoordinates_dot b ((basisCoordinates b).symm v) ((basisCoordinates b).symm v)
  simp only [ContinuousLinearEquiv.apply_symm_apply,real_inner_self_eq_norm_sq] at h
  change v ⬝ᵥ v=_ at h
  rw [hv] at h
  have hn := norm_nonneg ((basisCoordinates b).symm v)
  nlinarith

theorem reduced_query_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ E) (vis : VisibleFactorData d q (r+1))
    (v : Fin d → ℝ) (hB : vis.2*vis.2ᵀ=1) (hv : v ⬝ᵥ v=1)
    (horth : ∀ u∈queryColumns vis,v ⬝ᵥ u=0) :
    ambientQuery vis (reducedQueryDirection b vis v)=v := by
  have hh := head_zero vis v horth
  have hn := coordinate_norm_of_dot b _ (tail_unit vis v hB hv hh)
  have ht : tailQueryCoordinates vis v≠0 := by
    intro h
    simp [h] at hn
  have hu : reducedQueryDirection b vis v=tailQueryCoordinates vis v := by
    simp [reducedQueryDirection,unitCoordinateDirection,ht,coordinateSize,hn]
  rw [hu]
  simpa only [hh,Sum.elim_zero_zero,Matrix.mulVec_zero,zero_add] using ambient_query_split vis hB v

universe u
def compile (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    AmbientOraclePolicy d n S → VisibleOraclePolicy d r n q S
  | 0,_,_,_,_ => PUnit.unit
  | n+1,q,_,_,policy =>
      (⟨fun w => reducedQueryDirection (EuclideanSpace.basisFun (Fin (r+n+1)) ℝ) w.2 (policy.1.1 w.1),
        measurable_reducedQueryDirection _ _ _ measurable_snd (policy.1.2.comp measurable_fst)⟩,
        compile d r n (q+1) policy.2)

theorem compile_unit (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) : VisibleOraclePolicy.IsUnit d r n q (compile d r n q policy) := by
  induction n generalizing q S with
  | zero => trivial
  | succ n ih => exact ⟨fun _ => reducedQueryDirection_norm _ _ _,ih (q+1) policy.2⟩

def queryLog (d : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    AmbientOraclePolicy d n S → Matrix (Fin d) (Fin d) ℝ → S → List (Fin d → ℝ)
  | 0,_,_,_,_,_ => []
  | n+1,_,_,policy,W,x => policy.1.1 x :: queryLog d n policy.2 W (x,W *ᵥ policy.1.1 x)

def OrthonormalAfter {d : ℕ} (pre xs : List (Fin d → ℝ)) : Prop :=
  (∀ v∈xs,v ⬝ᵥ v=1) ∧ xs.Pairwise (fun v w => v ⬝ᵥ w=0) ∧
    ∀ v∈xs,∀ w∈pre,v ⬝ᵥ w=0

theorem orthonormalAfter_cons {d : ℕ} (pre xs : List (Fin d → ℝ)) (v : Fin d → ℝ)
    (h : OrthonormalAfter pre (v::xs)) :
    v ⬝ᵥ v=1 ∧ (∀ w∈pre,v ⬝ᵥ w=0) ∧ OrthonormalAfter (v::pre) xs := by
  obtain ⟨hunit,hpair,hcross⟩ := h
  have hp := List.pairwise_cons.mp hpair
  refine ⟨hunit v (List.mem_cons_self ..),hcross v (List.mem_cons_self ..),
    fun w hw => hunit w (List.mem_cons_of_mem v hw),hp.2,?_⟩
  intro w hw z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · rw [dotProduct_comm]
    exact hp.1 w hw
  · exact hcross w (List.mem_cons_of_mem v hw) z hz

end GradientHessian.AmbientOrthonormal
