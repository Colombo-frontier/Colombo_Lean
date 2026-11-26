import Bilevel.ChiSplitPayload
import Bilevel.ChiSplitFinePiecePrefix

/-! The actual split chain and its two terminal receivers retain source
r+1 and target r coordinates. Only the target tail must be small. -/
noncomputable section
open scoped BigOperators Topology
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

theorem value_prefix_value (n r : ℕ) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤1/4) :
    value n z=value n (ChiSplitFine.retainSplit n r z) := by
  unfold value
  change -ZeroChainPotential.phi (z.fst 0)+_=
    -ZeroChainPotential.phi (retain n (r+1) z.fst 0)+
      ∑ i : Fin n,edge (retain n r z.snd i.castSucc) (retain n (r+1) z.fst i.succ)
  rw [retain_apply,if_pos (by simp : (0:Fin (n+1)).val<r+1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<r
  · rw [retain_apply,if_pos (by simpa using hi),retain_apply,if_pos (by simpa using Nat.succ_lt_succ hi)]
  · have hb := hz i.castSucc (by change r≤ i.val;omega)
    rw [edge_inactive _ _ (by linarith only [hb]),retain_apply,if_neg (by simpa using hi),
      edge_inactive 0 _ (by norm_num)]

theorem chain_prefix_value (n r : ℕ) (ell h : ℝ) (hh : 0<h) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤h/4) :
    chain n ell h z=chain n ell h (ChiSplitFine.retainSplit n r z) := by
  have hs : ∀ k : Fin (n+1),r≤k.val → |(h⁻¹ • z).snd k|≤1/4 := by
    intro k hk
    change |h⁻¹*z.snd k|≤1/4
    rw [abs_mul,abs_inv,abs_of_pos hh,← div_eq_inv_mul]
    exact (div_le_iff₀ hh).mpr (by linarith only [hz k hk])
  have he := value_prefix_value n r (h⁻¹ • z) hs
  rw [(ChiSplitFine.retainSplit n r).map_smul h⁻¹ z] at he
  exact congrArg (fun a : ℝ => ell*h^2*a) he

theorem primitive_zero_on_blind {f : ℝ → ℝ} {h t : ℝ} (hh : 0<h)
    (hf : ∀ x,|x|≤h/4 → f x=0) (ht : |t|≤h/4) : primitive f t=0 := by
  unfold primitive
  have he : (∫ x in (0:ℝ)..t,f x)=(∫ _x in (0:ℝ)..t,(0:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hf
    change min 0 t≤x ∧ x≤max 0 t at hx
    have hlo : -(h/4)≤min 0 t := le_min (by linarith) (abs_le.mp ht).1
    have hhi : max 0 t≤h/4 := max_le (by linarith) (abs_le.mp ht).2
    exact abs_le.mpr ⟨hlo.trans hx.1,hx.2.trans hhi⟩
  rw [he]
  simp

theorem receiver_values_flat (A ν g h hp T t : ℝ) (hh : 0<h) (ht : |t|≤h/4) :
    positiveReceiver A ν g h hp t=0 ∧ negativeReceiver A g h T t=0 :=
  ⟨primitive_zero_on_blind hh (fun x hx => (receiver_slopes_flat A ν g h hp T x hh hx).1) ht,
    primitive_zero_on_blind hh (fun x hx => (receiver_slopes_flat A ν g h hp T x hh hx).2) ht⟩

theorem payload_prefix_value (n r : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤h/4) :
    payload n ell h A ν g hp T z=payload n ell h A ν g hp T (ChiSplitFine.retainSplit n r z) := by
  unfold payload
  rw [chain_prefix_value n r ell h hh z hz]
  change _+positiveReceiver A ν g h hp (z.snd (Fin.last n))+negativeReceiver A g h T (z.snd (Fin.last n))=
    _+positiveReceiver A ν g h hp (retain n r z.snd (Fin.last n))+negativeReceiver A g h T (retain n r z.snd (Fin.last n))
  rw [retain_apply]
  by_cases hr : n<r
  · rw [if_pos (by simpa using hr)]
  · rw [if_neg (by simpa using hr)]
    have ht := receiver_values_flat A ν g h hp T _ hh (hz (Fin.last n) (by simpa using Nat.le_of_not_gt hr))
    have hzero := receiver_values_flat A ν g h hp T 0 hh (by simpa using (show 0≤h/4 by positivity))
    rw [ht.1,ht.2,hzero.1,hzero.2]

theorem payload_prefix_eventually (n r : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|<h/4) :
    payload n ell h A ν g hp T =ᶠ[𝓝 z] payload n ell h A ν g hp T ∘ ChiSplitFine.retainSplit n r :=
  ChiSplitFine.value_prefix_eventually _ r (h/4) (payload_prefix_value n r ell h A ν g hp T hh) z hz

end Bilevel.ChiSplitChain
