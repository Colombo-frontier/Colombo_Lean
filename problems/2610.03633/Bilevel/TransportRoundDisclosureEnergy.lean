import Bilevel.TransportRoundPrefixEnergy

/-! The actual next-source disclosure after a completed round. It releases
exactly the next legal named column and erases that column from the tracked
future set. Its real energy cost is bounded after the frozen batch. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportObserver ProjectionGeometry
set_option maxHeartbeats 800000

theorem prefixName_some {n T : ℕ} (_hn : 0<n) (t : ℕ) (v : Vertex n) (i : Fin T)
    (hi : prefixNames n T t v 0=some i) : v=0 ∧ i.val*n=t+1 := by
  classical
  unfold prefixNames at hi
  split_ifs at hi with hv hT
  have he : (⟨(t+1)/n,hT⟩ : Fin T)=i := Option.some.inj hi
  have hi' : i.val=(t+1)/n := congrArg Fin.val he.symm
  refine ⟨hv.1,?_⟩
  have hh := Nat.mod_add_div (t+1) n
  rw [hv.2,zero_add] at hh
  rw [hi',Nat.mul_comm]
  exact hh

theorem nextProtected_of_no_name {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n)
    (h : prefixNames n T t v 0=none) (i : Fin T) : Protected (t+1) v i ↔ PostProtected t v i := by
  constructor
  · intro hi
    cases v using Fin.cases with
    | zero =>
      by_contra hold
      have he := new_source_only_after_completion hn t i hi hold
      have hTi : (t+1)/n<T := by rw [← he.2.2]; exact i.isLt
      simp only [prefixNames,he.2.1,and_self,ite_true,dif_pos hTi] at h
      cases h
    | succ v =>
      refine ⟨hi,?_⟩
      dsimp [Protected] at hi
      omega
  · exact fun h => h.1

theorem nextProtected_of_name {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (i : Fin T)
    (hi : prefixNames n T t v 0=some i) (j : Fin T) :
    Protected (t+1) v j ↔ PostProtected t v j ∨ j=i := by
  obtain ⟨hv,hi'⟩ := prefixName_some hn t v i hi
  subst v
  constructor
  · intro hj
    by_cases hold : PostProtected t (0 : Vertex n) j
    · exact Or.inl hold
    · apply Or.inr
      have hj' := (new_source_only_after_completion hn t j hj hold).1
      apply Fin.ext
      nlinarith
  · rintro (hold | rfl)
    · exact hold.1
    · simpa only [Protected,Fin.val_zero,Nat.add_zero,hi'] using le_rfl

theorem nextFuture_none {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (h : prefixNames n T t v 0=none) :
    oldFuture T (t+1) v=postFuture T t v := by
  classical
  ext i
  simp only [oldFuture,postFuture,Finset.mem_filter,Finset.mem_univ,true_and,nextProtected_of_no_name hn t v h]

theorem nextFuture_some {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (i : Fin T)
    (hi : prefixNames n T t v 0=some i) : oldFuture T (t+1) v=(postFuture T t v).erase i := by
  classical
  ext j
  simp only [oldFuture,postFuture,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,
    nextProtected_of_name hn t v i hi,not_or]
  tauto

theorem prefixName_blind {n T : ℕ} (hn : 0<n) (t : ℕ) (v : Vertex n) (i : Fin T)
    (hi : prefixNames n T t v 0=some i) : i∈postFuture T t v := by
  classical
  obtain ⟨hv,he⟩ := prefixName_some hn t v i hi
  subst v
  simp only [postFuture,Finset.mem_filter,Finset.mem_univ,true_and,PostProtected,he]
  omega

def sourceDisclosure {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D) :
    Generators n D (m+1) := augment g (disclosures T hT (prefixNames n T t) z)

theorem sourceDisclosure_none {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (v : Vertex n) (h : prefixNames n T t v 0=none) : known (sourceDisclosure hT t g z) v=known g v := by
  have he : disclosures T hT (prefixNames n T t) z v = fun _ : Fin 1 => 0 := by
    funext j
    change (match prefixNames n T t v 0 with | none => 0 | some i => frame T hT z v i)=0
    rw [h]
  rw [sourceDisclosure,augment_span,he,singleton_family_span,Submodule.span_zero_singleton,sup_bot_eq]

theorem sourceDisclosure_some {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (v : Vertex n) (i : Fin T) (hi : prefixNames n T t v 0=some i) :
    known (sourceDisclosure hT t g z) v=known g v⊔Submodule.span ℝ {frame T hT z v i} := by
  have he : disclosures T hT (prefixNames n T t) z v = fun _ : Fin 1 => frame T hT z v i := by
    funext j
    change (match prefixNames n T t v 0 with | none => 0 | some i => frame T hT z v i)=frame T hT z v i
    rw [hi]
  rw [sourceDisclosure,augment_span,he,singleton_family_span]

theorem sourceDisclosure_row_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (v : Vertex n)
    (hsmall : frameEnergy (known g v) (frame T hT z v) (postFuture T t v)≤(1:ℝ)/4096) :
    frameEnergy (known (sourceDisclosure hT t g z) v) (frame T hT z v) (oldFuture T (t+1) v) ≤
      2*frameEnergy (known g v) (frame T hT z v) (postFuture T t v) := by
  classical
  cases hi : prefixNames n T t v 0 with
  | none =>
    rw [sourceDisclosure_none hT t g z v hi,nextFuture_none hn t v hi]
    have hh := frameEnergy_nonneg (known g v) (frame T hT z v) (postFuture T t v)
    linarith
  | some i =>
    rw [sourceDisclosure_some hT t g z v i hi,nextFuture_some hn t v i hi]
    let e := frameEnergy (known g v) (frame T hT z v) (postFuture T t v)
    have he : energy (known g v) (frame T hT z v i)≤e :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖project (known g v) (frame T hT z v j)‖) (prefixName_blind hn t v i hi)
    have hnon : 0≤e := frameEnergy_nonneg _ _ _
    have ho : ∀ j∈(postFuture T t v).erase i, ⟪frame T hT z v j,frame T hT z v i⟫=0 := by
      intro j hj
      exact (frame_orthonormal T hT z v).2 (Finset.ne_of_mem_erase hj)
    have hh := named_column_energy (known g v) (frame T hT z v) ((postFuture T t v).erase i)
      (frame T hT z v i) ((frame_orthonormal T hT z v).norm_eq_one i) hnon (by dsimp [e]; linarith) he ho
    have hcoeff : 1+2*e≤2 := by dsimp [e]; linarith
    have hmono := frameEnergy_mono_indices (known g v) (frame T hT z v) (Finset.erase_subset i (postFuture T t v))
    exact hh.trans ((mul_le_mul_of_nonneg_right hcoeff (frameEnergy_nonneg _ _ _)).trans
      (mul_le_mul_of_nonneg_left hmono (by norm_num)))

theorem sourceDisclosure_total_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hsmall : TransportRoundEnergy.total (known g) (frame T hT z) (postFuture T t)≤(1:ℝ)/4096) :
    TransportRoundEnergy.total (known (sourceDisclosure hT t g z)) (frame T hT z) (oldFuture T (t+1)) ≤
      2*TransportRoundEnergy.total (known g) (frame T hT z) (postFuture T t) := by
  unfold TransportRoundEnergy.total
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact sourceDisclosure_row_energy hT hn t g z v ((TransportRoundEnergy.row_le_total _ _ _ v).trans hsmall)

end Bilevel.TransportRound
