import Bilevel.TransportRoundPrefixEnergy

/-! Protected columns and future sets in the concrete post-batch analysis
store. The grant remains an analysis object, never a source of batch probes. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork

theorem postGrant_prefix {n D m : ℕ} (T : ℕ) (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hg : ∀ v i, Protected t v i → frame T hT z v i∈known g v) :
    ∀ v i, PostProtected t v i → frame T hT z v i∈known (postGrant T hT t g z) v := by
  intro v i hi
  cases hj : postNew (T := T) t v with
  | none =>
    rw [postGrant_known_none T hT t g z v hj]
    exact hg v i ((postNew_none t v hj i).mp hi)
  | some j =>
    rw [postGrant_known_some T hT t g z v j hj]
    rcases (postNew_iff hn t v j hj i).mp hi with hold | rfl
    · exact (show known g v≤known g v⊔Submodule.span ℝ {frame T hT z v j} from le_sup_left) (hg v i hold)
    · exact (show Submodule.span ℝ {frame T hT z v i}≤known g v⊔Submodule.span ℝ {frame T hT z v i}
        from le_sup_right) (Submodule.mem_span_singleton_self _)

theorem postGrant_keeps {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (v : Vertex n) : known g v≤known (postGrant T hT t g z) v := by
  rw [postGrant,augment_span]
  exact le_sup_left

def oldProtected {n : ℕ} (T t : ℕ) (v : Vertex n) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter (Protected t v)

theorem oldFuture_eq_complement {n : ℕ} (T t : ℕ) (v : Vertex n) :
    oldFuture T t v=Finset.univ\oldProtected T t v := by
  classical
  ext i
  simp only [oldFuture,oldProtected,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]

theorem postFuture_dst {n : ℕ} (T t : ℕ) (e : Edge n) :
    postFuture T t (dst e)=oldFuture T t (src e) := by
  classical
  ext i
  simp only [postFuture,oldFuture,Finset.mem_filter,Finset.mem_univ,true_and,post_dst_iff_src]

theorem postFuture_src_subset {n : ℕ} (T t : ℕ) (e : Edge n) :
    postFuture T t (src e)⊆oldFuture T t (src e) := by
  classical
  intro i hi
  simp only [postFuture,oldFuture,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact global_future_src t e i hi

end Bilevel.TransportRound
