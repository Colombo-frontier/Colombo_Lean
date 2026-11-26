import Bilevel.TransportRoundPhase
import Bilevel.TransportRoundEnergy
import Bilevel.TransportRoundInitialization

/-! A concrete phase ledger for the executed chain. For analysis only, the
post-batch protected column is granted before processing edge innovations.
The grant is already contained in the actual frozen-batch output, adds at
most one column per layer, and doubles the aggregate blind energy at most.
It is never made available as a current-batch algorithm input. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportObserver ProjectionGeometry
set_option maxHeartbeats 800000

theorem protected_post {n T : ℕ} (t : ℕ) (v : Vertex n) (i : Fin T) :
    Protected t v i → PostProtected t v i := by
  dsimp [Protected,PostProtected]
  omega

theorem post_dst_iff_src {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T) :
    PostProtected t (dst e) i ↔ Protected t (src e) i := by
  dsimp [Protected,PostProtected,src,dst]
  omega

theorem post_new_unique {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (i j : Fin T)
    (hi : PostProtected t v i ∧ ¬Protected t v i)
    (hj : PostProtected t v j ∧ ¬Protected t v j) : i=j := by
  have h1 : i.val*n+v.val=t+1 := by dsimp [PostProtected,Protected] at hi; omega
  have h2 : j.val*n+v.val=t+1 := by dsimp [PostProtected,Protected] at hj; omega
  apply Fin.ext
  nlinarith

def postNew {n T : ℕ} (t : ℕ) (v : Vertex n) : Option (Fin T) := by
  classical
  exact if h : ∃ i : Fin T, PostProtected t v i ∧ ¬Protected t v i then some (Classical.choose h) else none

theorem postNew_some {n T : ℕ} (t : ℕ) (v : Vertex n) (i : Fin T) (hi : postNew t v=some i) :
    PostProtected t v i ∧ ¬Protected t v i := by
  classical
  unfold postNew at hi
  split_ifs at hi with h
  · have he : Classical.choose h=i := Option.some.inj hi
    exact he ▸ Classical.choose_spec h

theorem postNew_none {n T : ℕ} (t : ℕ) (v : Vertex n) (h : postNew (T := T) t v=none) (i : Fin T) :
    PostProtected t v i ↔ Protected t v i := by
  constructor
  · intro hi
    by_contra hn
    have hex : ∃ j : Fin T, PostProtected t v j ∧ ¬Protected t v j := ⟨i,hi,hn⟩
    simp only [postNew,dif_pos hex] at h
    cases h
  · exact protected_post t v i

theorem postNew_iff {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (i : Fin T)
    (hi : postNew t v=some i) (j : Fin T) :
    PostProtected t v j ↔ Protected t v j ∨ j=i := by
  have hi' := postNew_some t v i hi
  constructor
  · intro hj
    by_cases hold : Protected t v j
    · exact Or.inl hold
    · exact Or.inr (post_new_unique hn t v j i ⟨hj,hold⟩ hi')
  · rintro (hold | rfl)
    · exact protected_post t v j hold
    · exact hi'.1

def oldFuture {n : ℕ} (T t : ℕ) (v : Vertex n) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter (fun i => ¬Protected t v i)

def postFuture {n : ℕ} (T t : ℕ) (v : Vertex n) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter (fun i => ¬PostProtected t v i)

theorem postFuture_none {n : ℕ} (T t : ℕ) (v : Vertex n) (h : postNew (T := T) t v=none) :
    postFuture T t v=oldFuture T t v := by
  classical
  ext i
  simp only [postFuture,oldFuture,Finset.mem_filter,Finset.mem_univ,true_and,postNew_none t v h]

theorem postFuture_some {n : ℕ} (T t : ℕ) (hn : 0<n) (v : Vertex n) (i : Fin T)
    (hi : postNew t v=some i) : postFuture T t v=(oldFuture T t v).erase i := by
  classical
  ext j
  simp only [postFuture,oldFuture,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,
    postNew_iff hn t v i hi,not_or]
  tauto

def postGrant {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D) :
    Generators n D (m+1) := augment g (disclosures T hT (fun v (_ : Fin 1) => postNew t v) z)

theorem postGrant_known_none {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (v : Vertex n) (h : postNew (T := T) t v=none) :
    known (postGrant T hT t g z) v=known g v := by
  rw [postGrant,augment_span]
  have he : disclosures T hT (fun v (_ : Fin 1) => postNew t v) z v = fun _ : Fin 1 => 0 := by
    funext j
    simp only [disclosures,h]
  rw [he,singleton_family_span,Submodule.span_zero_singleton,sup_bot_eq]

theorem postGrant_known_some {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (v : Vertex n) (i : Fin T) (hi : postNew t v=some i) :
    known (postGrant T hT t g z) v=known g v⊔Submodule.span ℝ {frame T hT z v i} := by
  rw [postGrant,augment_span]
  have he : disclosures T hT (fun v (_ : Fin 1) => postNew t v) z v = fun _ : Fin 1 => frame T hT z v i := by
    funext j
    simp only [disclosures,hi]
  rw [he,singleton_family_span]

theorem execute_post_prefix {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hg : ∀ v i, Protected t v i → frame T hT z v i∈known g v) :
    ∀ v i, PostProtected t v i → frame T hT z v i∈known (execute g z) v := by
  intro v i hi
  cases v using Fin.cases with
  | zero => exact keeps_old g z 0 (hg 0 i hi.2)
  | succ e =>
    have hp := (post_dst_iff_src t e i).mp hi
    have hm := forward_whole_space g z e
      (show z.2 e • frame T hT z (src e) i ∈ (known g (src e)).map (OrthogonalAction.isometry D (z.2 e)).toLinearEquiv.toLinearMap from
        ⟨frame T hT z (src e) i,hg (src e) i hp,rfl⟩)
    simpa only [edge_frame] using hm

theorem postGrant_le_execute {n D m : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hg : ∀ v i, Protected t v i → frame T hT z v i∈known g v) (v : Vertex n) :
    known (postGrant T hT t g z) v≤known (execute g z) v := by
  cases hi : postNew (T := T) t v with
  | none => rw [postGrant_known_none T hT t g z v hi]; exact keeps_old g z v
  | some i =>
    rw [postGrant_known_some T hT t g z v i hi]
    apply sup_le (keeps_old g z v)
    apply Submodule.span_le.mpr
    intro x hx
    have he : x=frame T hT z v i := Set.mem_singleton_iff.mp hx
    rw [he]
    exact execute_post_prefix T hT t g z hg v i (postNew_some t v i hi).1

theorem postGrant_energy {n D m : ℕ} (T : ℕ) (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (v : Vertex n)
    (hsmall : frameEnergy (known g v) (frame T hT z v) (oldFuture T t v)≤(1:ℝ)/4096) :
    frameEnergy (known (postGrant T hT t g z) v) (frame T hT z v) (postFuture T t v) ≤
      2*frameEnergy (known g v) (frame T hT z v) (oldFuture T t v) := by
  classical
  cases hi : postNew (T := T) t v with
  | none =>
    rw [postGrant_known_none T hT t g z v hi,postFuture_none T t v hi]
    have hh := frameEnergy_nonneg (known g v) (frame T hT z v) (oldFuture T t v)
    linarith
  | some i =>
    rw [postGrant_known_some T hT t g z v i hi,postFuture_some T t hn v i hi]
    let e := frameEnergy (known g v) (frame T hT z v) (oldFuture T t v)
    have hine : i∈oldFuture T t v := by simpa only [oldFuture,Finset.mem_filter,Finset.mem_univ,true_and] using (postNew_some t v i hi).2
    have he : energy (known g v) (frame T hT z v i)≤e :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖project (known g v) (frame T hT z v j)‖) hine
    have hnon : 0≤e := frameEnergy_nonneg _ _ _
    have ho : ∀ j∈(oldFuture T t v).erase i, ⟪frame T hT z v j,frame T hT z v i⟫=0 := by
      intro j hj
      exact (frame_orthonormal T hT z v).2 (Finset.ne_of_mem_erase hj)
    have hh := named_column_energy (known g v) (frame T hT z v) ((oldFuture T t v).erase i)
      (frame T hT z v i) ((frame_orthonormal T hT z v).norm_eq_one i) hnon (by dsimp [e]; linarith)
      he ho
    have hcoeff : 1+2*e≤2 := by dsimp [e]; linarith
    have hmono := frameEnergy_mono_indices (known g v) (frame T hT z v) (Finset.erase_subset i (oldFuture T t v))
    exact hh.trans ((mul_le_mul_of_nonneg_right hcoeff (frameEnergy_nonneg _ _ _)).trans
      (mul_le_mul_of_nonneg_left hmono (by norm_num)))

theorem postGrant_total_energy {n D m : ℕ} (T : ℕ) (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hsmall : TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)≤(1:ℝ)/4096) :
    TransportRoundEnergy.total (known (postGrant T hT t g z)) (frame T hT z) (postFuture T t) ≤
      2*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) := by
  unfold TransportRoundEnergy.total
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact postGrant_energy T hT hn t g z v ((TransportRoundEnergy.row_le_total _ _ _ v).trans hsmall)

end Bilevel.TransportRound
