import Bilevel.ChiBoundedChainEstimates
import Bilevel.ChiBoundedChainMaskJets

/-! Actual order-three derivatives of the revised incoming source. The even
activation and bounded Psi are used throughout; no old signed edge is identified
with this source. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential
open ZeroChainResidualBounds (projection_norm_le scalar_linear_jet_bound jet_mul_bound
  jet_mul_zero_left jet_mul_zero_right)

theorem chain_profile_bound : ∃ K : ℝ,1≤K ∧ ∀ j : Fin 4,∀ t,
    |iteratedDeriv j.val psi t|≤K ∧ |iteratedDeriv j.val phi t|≤K := by
  have he (j : Fin 4) := psi_jet_bound j.val (show j.val≤3 by omega)
  choose A hA ha using he
  obtain ⟨B,hB,hb⟩ := phi_uniform_jet_bound
  have hs : 0≤∑ j,A j := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨1+B+∑ j,A j,by linarith,fun j t => ⟨?_,?_⟩⟩
  · have hj := Finset.single_le_sum (fun k (_ : k∈Finset.univ) => hA k) (Finset.mem_univ j)
    exact (ha j t).trans (by linarith)
  · exact (hb j t).trans (by linarith)

theorem evenGate_linear_jet {n : ℕ} (p : Space n →L[ℝ] ℝ) (z : Space n)
    (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (evenGate ∘ p) z =
      iteratedFDeriv ℝ k (psi ∘ p) z+iteratedFDeriv ℝ k (psi ∘ (-p)) z := by
  have hk' : (k : WithTop ℕ∞)≤3 := by exact_mod_cast hk
  have he : evenGate ∘ p=(fun w => (psi ∘ p) w+(psi ∘ (-p)) w) := rfl
  rw [he,iteratedFDeriv_add_apply'
    ((psi_contDiff.comp p.contDiff).of_le hk').contDiffAt
    ((psi_contDiff.comp (-p).contDiff).of_le hk').contDiffAt]

theorem evenGate_linear_jet_bound {n : ℕ} (p : Space n →L[ℝ] ℝ) (hp : ‖p‖≤1)
    (z : Space n) (k : ℕ) (hk : k≤3) (K : ℝ) (hK : 0≤K)
    (hb : ∀ t,|iteratedDeriv k psi t|≤K) :
    ‖iteratedFDeriv ℝ k (evenGate ∘ p) z‖≤2*K := by
  rw [evenGate_linear_jet p z k hk]
  have h₁ := scalar_linear_jet_bound psi_contDiff p hp z k hk K hK (hb _)
  have h₂ := scalar_linear_jet_bound psi_contDiff (-p) (by simpa using hp) z k hk K hK (hb _)
  exact (norm_add_le _ _).trans (by linarith)

theorem evenGate_linear_flat {n : ℕ} (p : Space n →L[ℝ] ℝ) (hp : ‖p‖≤1)
    (z : Space n) (hz : |p z|≤1/2) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (evenGate ∘ p) z=0 := by
  have ht (q : Space n →L[ℝ] ℝ) (hq : ‖q‖≤1) (hqz : q z≤1/2) :
      iteratedFDeriv ℝ k (psi ∘ q) z=0 := by
    apply norm_le_zero_iff.mp
    apply scalar_linear_jet_bound psi_contDiff q hq z k hk 0 le_rfl
    rw [psi_flat_left k hk _ hqz,abs_zero]
  rw [evenGate_linear_jet p z k hk,ht p hp (abs_le.mp hz).2,
    ht (-p) (by simpa using hp) (by change -p z≤1/2;linarith [(abs_le.mp hz).1]),zero_add]

def incomingJetBound (K : ℝ) (k : ℕ) : ℝ :=
  K+∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*(2*K)*K

theorem incomingJetBound_nonneg {K : ℝ} (hK : 0≤K) (k : ℕ) :
    0 ≤ incomingJetBound K k := by unfold incomingJetBound;positivity

theorem incoming_jet_bound {K : ℝ} (hK : 0≤K)
    (hb : ∀ j : Fin 4,∀ t,|iteratedDeriv j.val psi t|≤K ∧ |iteratedDeriv j.val phi t|≤K)
    (n : ℕ) (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (incoming n i) z‖ ≤ incomingJetBound K k := by
  have hs : 0≤∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*(2*K)*K := by positivity
  refine Fin.cases ?_ (fun l => ?_) i
  · change ‖iteratedFDeriv ℝ k (-(phi ∘ EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1)))) z‖≤_
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact (scalar_linear_jet_bound (phi_contDiff 3) _ (projection_norm_le _) z k hk K hK
      (hb ⟨k,by omega⟩ _).2).trans (by unfold incomingJetBound;linarith)
  · let p := EuclideanSpace.proj (𝕜:=ℝ) l.castSucc
    let q := EuclideanSpace.proj (𝕜:=ℝ) l.succ
    have hh := jet_mul_bound ((evenGate_contDiff 3).comp p.contDiff)
      ((phi_contDiff 3).comp q.contDiff) z k hk (fun _ => 2*K) (fun _ => K)
      (fun _ => by positivity)
      (fun j hj => evenGate_linear_jet_bound p (projection_norm_le _) z j (by omega) K hK
        (fun t => (hb ⟨j,by omega⟩ t).1))
      (fun j hj => scalar_linear_jet_bound (phi_contDiff 3) q (projection_norm_le _) z j
        (by omega) K hK (hb ⟨j,by omega⟩ _).2)
    have he : incoming n l.succ=-(fun w => evenGate (p w)*phi (q w)) := by
      funext w
      simp [incoming,p,q]
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact hh.trans (by unfold incomingJetBound;linarith)

theorem incoming_succ_flat_jet {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc|≤1/2) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (incoming n i.succ) z=0 := by
  let p := EuclideanSpace.proj (𝕜:=ℝ) i.castSucc
  let q := EuclideanSpace.proj (𝕜:=ℝ) i.succ
  have hh := jet_mul_zero_left ((evenGate_contDiff 3).comp p.contDiff)
    ((phi_contDiff 3).comp q.contDiff) z k hk
    (fun j hj => evenGate_linear_flat p (projection_norm_le _) z hz j (by omega))
  have he : incoming n i.succ=-(fun w => evenGate (p w)*phi (q w)) := by
    funext w
    simp [incoming,p,q]
  rw [he,iteratedFDeriv_neg_apply]
  simpa only [neg_eq_zero] using hh

end Bilevel.ChiBoundedChain
