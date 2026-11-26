import Bilevel.TransportNetworkPhysical
import Bilevel.TransportRoundController

/-! The actual transported quadratic Hessian is evaluated from one frozen
edge batch. Only old generators and current query vectors are batch inputs;
no returned edge action is transported again in this evaluation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Bilevel.TransportHierarchy
open EuclideanGaussian TransportNetwork OrthogonalAction EndpointTransportResponse
open EndpointTransportMatrix TransportRound
set_option maxHeartbeats 800000

def forwardQuerySlot (n m p : ℕ) (e : Edge n) (a : Fin p) :
    Fin (n*(m+p)+n*(m+p)) := Fin.castAdd (n*(m+p))
      (finProdFinEquiv (e,Fin.natAdd m a))

def reverseQuerySlot (n m p : ℕ) (e : Edge n) (a : Fin p) :
    Fin (n*(m+p)+n*(m+p)) := Fin.natAdd (n*(m+p))
      (finProdFinEquiv (e,Fin.natAdd m a))

theorem batch_forwardQuery {n D m p : ℕ} (g : Generators n D m)
    (q : Queries n D p) (z : Latent n D) (e : Edge n) (a : Fin p) :
    batch (augment g q) z (forwardQuerySlot n m p e a)=z.2 e • q (src e) a := by
  simp only [batch,batchObservation,probes,forwardQuerySlot,Fin.append_left,
    forwardProbes,Equiv.symm_apply_apply,probeObservation,Bool.false_eq_true,
    ite_false,forwardObservation,augment,Fin.append_right]

theorem batch_reverseQuery {n D m p : ℕ} (g : Generators n D m)
    (q : Queries n D p) (z : Latent n D) (e : Edge n) (a : Fin p) :
    batch (augment g q) z (reverseQuerySlot n m p e a)=(z.2 e)⁻¹ • q (dst e) a := by
  simp only [batch,batchObservation,probes,reverseQuerySlot,Fin.append_right,
    reverseProbes,Equiv.symm_apply_apply,probeObservation,ite_true,
    reverseObservation,augment,Fin.append_right]

theorem physicalRotations_reverse {n D : ℕ} (z : Latent (n+1) D)
    (e : Edge (n+1)) (x : Space D) :
    physicalRotations z (src e) ((physicalRotations z (dst e)).symm x)=(z.2 e)⁻¹ • x := by
  apply (isometry D (z.2 e)).injective
  change z.2 e • _=z.2 e • ((z.2 e)⁻¹ • x)
  rw [←physicalRotations_forward,LinearIsometryEquiv.apply_symm_apply,smul_inv_smul]

def batchPair {n D m p : ℕ} (q : Queries (n+1) D p)
    (y : Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D)
    (a : Fin p) (i j : Index n) : Space D :=
  if j=i then q j a
  else if hf : j.val+1=i.val then
    y (forwardQuerySlot (n+1) m p ⟨j.val,by omega⟩ a)
  else if hr : i.val+1=j.val then
    y (reverseQuerySlot (n+1) m p ⟨i.val,by omega⟩ a)
  else 0

theorem matrix_batchPair {n D m p : ℕ} (g : Generators (n+1) D m)
    (q : Queries (n+1) D p) (z : Latent (n+1) D) (a : Fin p) (i j : Index n) :
    matrix n i j • batchPair q (batch (augment g q) z) a i j =
      matrix n i j • physicalRotations z i ((physicalRotations z j).symm (q j a)) := by
  by_cases he : j=i
  · subst j
    simp only [batchPair,ite_true,LinearIsometryEquiv.apply_symm_apply]
  · by_cases hf : j.val+1=i.val
    · let e : Edge (n+1) := ⟨j.val,by omega⟩
      have hs : src e=j := Fin.ext rfl
      have hd : dst e=i := Fin.ext hf
      simp only [batchPair,if_neg he,dif_pos hf]
      rw [batch_forwardQuery]
      change matrix n i j • z.2 e • q (src e) a = _
      have hh := physicalRotations_edge z e (q j a)
      rw [hs,hd] at hh
      rw [hs,hh]
    · by_cases hr : i.val+1=j.val
      · let e : Edge (n+1) := ⟨i.val,by omega⟩
        have hs : src e=i := Fin.ext rfl
        have hd : dst e=j := Fin.ext hr
        simp only [batchPair,if_neg he,dif_neg hf,dif_pos hr]
        rw [batch_reverseQuery]
        change matrix n i j • (z.2 e)⁻¹ • q (dst e) a = _
        have hh := physicalRotations_reverse z e (q j a)
        rw [hs,hd] at hh
        rw [hd,hh]
      · have hm : matrix n i j=0 := by
          rw [matrix,baseMatrix_zero n i j he hr hf,zero_div]
        simp only [hm,zero_smul]

def batchHessian {n D m p : ℕ} (δ : ℝ) (q : Queries (n+1) D p)
    (y : Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D) (a : Fin p) : Physical n D :=
  physical (fun i => δ • ∑ j : Index n,matrix n i j • batchPair q y a i j)

theorem batchHessian_actual {n D m p : ℕ} (δ : ℝ) (g : Generators (n+1) D m)
    (q : Queries (n+1) D p) (z : Latent (n+1) D) (a : Fin p) :
    batchHessian δ q (batch (augment g q) z) a=
      physicalHessian δ (physicalRotations z) (physical (fun i => q i a)) := by
  rw [physicalHessian_apply]
  ext i d
  change (δ • ∑ j : Index n,matrix n i j • batchPair q (batch (augment g q) z) a i j) d=
    (δ • physicalRotations z i (∑ j : Index n,matrix n i j •
      (physicalRotations z j).symm (q j a))) d
  simp_rw [matrix_batchPair,map_sum,map_smul]

theorem batchPair_measurable {n D m p : ℕ} (a : Fin p) (i j : Index n) :
    Measurable (fun z : Queries (n+1) D p ×
      (Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D) => batchPair z.1 z.2 a i j) := by
  unfold batchPair
  split_ifs
  · exact (measurable_pi_apply a).comp ((measurable_pi_apply j).comp measurable_fst)
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact measurable_const

theorem batchHessian_measurable {n D m p : ℕ}
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] (δ : ℝ) (a : Fin p) :
    Measurable (fun z : Queries (n+1) D p ×
      (Fin ((n+1)*(m+p)+(n+1)*(m+p)) → Space D) => batchHessian δ z.1 z.2 a) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Index n => Block D)).measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (Finset.measurable_sum _ (fun j _ => (batchPair_measurable (n:=n) (D:=D) (m:=m) (p:=p) a i j).const_smul (matrix n i j))).const_smul δ

end Bilevel.TransportHierarchy

