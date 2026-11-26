import Bilevel.TransportRoundAngle
import Bilevel.TransportControllerQuery

/-! A concrete aggregate-energy ledger for finitely many global and local
spaces. Actual query insertion, named disclosure, and transport block
updates give the fixed numerical recurrence factors used in the observer.
Probability and legality of the executed schedule remain separate. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportRoundEnergy
open EuclideanGaussian ProjectionGeometry TransportObserver
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {r T : ℕ}

def total (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E) (I : Fin r → Finset (Fin T)) : ℝ :=
  ∑ j, frameEnergy (W j) (V j) (I j)

theorem total_nonneg (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E) (I : Fin r → Finset (Fin T)) :
    0 ≤ total W V I := Finset.sum_nonneg (fun _ _ => frameEnergy_nonneg _ _ _)

theorem row_le_total (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (j : Fin r) : frameEnergy (W j) (V j) (I j) ≤ total W V I :=
  Finset.single_le_sum (fun _ _ => frameEnergy_nonneg _ _ _) (Finset.mem_univ j)

theorem sum_update (f : Fin r → ℝ) (j : Fin r) (x : ℝ) :
    ∑ i, Function.update f j x i = (∑ i, f i)-f j+x := by
  have he : Function.update f j x = fun i => f i+if i=j then x-f j else 0 := by
    funext i
    by_cases hi : i=j
    · subst i; simp
    · simp [Function.update_of_ne hi,hi]
  rw [he,Finset.sum_add_distrib]
  simp
  ring

theorem total_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (j : Fin r) (W' : Submodule ℝ E) (I' : Finset (Fin T)) :
    total (Function.update W j W') V (Function.update I j I') =
      total W V I-frameEnergy (W j) (V j) (I j)+frameEnergy W' (V j) I' := by
  have he : (fun i => frameEnergy (Function.update W j W' i) (V i) (Function.update I j I' i)) =
      Function.update (fun i => frameEnergy (W i) (V i) (I i)) j (frameEnergy W' (V j) I') := by
    funext i
    by_cases hi : i=j
    · subst i; simp
    · simp only [Function.update_of_ne hi]
  unfold total
  rw [he,sum_update]

theorem query_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (j : Fin r) (q : E) {a : ℝ}
    (ha : frameEnergy (W j ⊔ Submodule.span ℝ {q}) (V j) (I j)-frameEnergy (W j) (V j) (I j) ≤ a) :
    total (Function.update W j (W j ⊔ Submodule.span ℝ {q})) V I ≤ total W V I+a := by
  have hi : Function.update I j (I j)=I := Function.update_eq_self j I
  have hh := total_update W V I j (W j ⊔ Submodule.span ℝ {q}) (I j)
  rw [hi] at hh
  linarith

theorem shrink_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (j : Fin r) (J : Finset (Fin T)) (hJ : J⊆I j) :
    total W V (Function.update I j J) ≤ total W V I := by
  have hw : Function.update W j (W j)=W := Function.update_eq_self j W
  have hh := total_update W V I j (W j) J
  rw [hw] at hh
  have hm := frameEnergy_mono_indices (W j) (V j) hJ
  linarith

theorem block_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (src dst : Fin r) (O : E ≃ₗᵢ[ℝ] E) (R : Submodule ℝ E)
    (hR : R≤W src) (hV : ∀ i, V dst i=O (V src i)) (hI : I dst⊆I src)
    (hang : ∀ x∈R.map O.toLinearEquiv.toLinearMap, ‖project (W dst) x‖≤‖x‖/2) :
    total (Function.update W dst (W dst ⊔ R.map O.toLinearEquiv.toLinearMap)) V I ≤ 17*total W V I := by
  have hsrc := row_le_total W V I src
  have hdst := row_le_total W V I dst
  have hh := transported_frame_energy_update O (W dst) R (W src) hR (V src) (I dst) (I src) hI hsrc hang
  have he : (fun i => O (V src i))=V dst := funext (fun i => (hV i).symm)
  rw [he] at hh
  have hu := total_update W V I dst (W dst ⊔ R.map O.toLinearEquiv.toLinearMap) (I dst)
  rw [Function.update_eq_self dst I] at hu
  linarith

theorem copy_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (src dst : Fin r) (hV : V dst=V src) (hI : I dst⊆I src) :
    total (Function.update W dst (W src)) V I ≤ 2*total W V I := by
  have hh := total_update W V I dst (W src) (I dst)
  rw [Function.update_eq_self dst I] at hh
  have hm : frameEnergy (W src) (V dst) (I dst)≤total W V I := by
    rw [hV]
    exact (frameEnergy_mono_indices (W src) (V src) hI).trans (row_le_total W V I src)
  have hn := frameEnergy_nonneg (W dst) (V dst) (I dst)
  linarith

theorem named_update (W : Fin r → Submodule ℝ E) (V : Fin r → Fin T → E)
    (I : Fin r → Finset (Fin T)) (j : Fin r) (i : Fin T) (hi : i∈I j)
    (hV : Orthonormal ℝ (V j)) (hsmall : total W V I≤(1:ℝ)/4096) :
    total (Function.update W j (W j ⊔ Submodule.span ℝ {V j i})) V
      (Function.update I j ((I j).erase i)) ≤ 2*total W V I := by
  have hnon := total_nonneg W V I
  have he : energy (W j) (V j i)≤total W V I :=
    (Finset.single_le_sum (fun k _ => sq_nonneg ‖project (W j) (V j k)‖) hi).trans (row_le_total W V I j)
  have ho : ∀ k∈(I j).erase i, ⟪V j k,V j i⟫=0 := by
    intro k hk
    exact hV.2 (Finset.ne_of_mem_erase hk)
  have hh := named_column_energy (W j) (V j) ((I j).erase i) (V j i)
    (hV.norm_eq_one i) hnon (by linarith) he ho
  have hm := frameEnergy_mono_indices (W j) (V j) (Finset.erase_subset i (I j))
  have hb : frameEnergy (W j ⊔ Submodule.span ℝ {V j i}) (V j) ((I j).erase i) ≤
      2*frameEnergy (W j) (V j) (I j) := by
    have hn := frameEnergy_nonneg (W j) (V j) ((I j).erase i)
    have hc : 1+2*total W V I≤2 := by linarith
    exact hh.trans ((mul_le_mul_of_nonneg_right hc hn).trans (mul_le_mul_of_nonneg_left hm (by norm_num)))
  have hu := total_update W V I j (W j ⊔ Submodule.span ℝ {V j i}) ((I j).erase i)
  have hj := row_le_total W V I j
  linarith

end Bilevel.TransportRoundEnergy
