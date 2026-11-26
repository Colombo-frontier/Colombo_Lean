import Bilevel.ChiSplitCenteredPayload
import Bilevel.ChiSplitPrefixGradient

/-! Split-prefix evaluation with independently chosen source and target
counts. Centered payloads need only old source columns. Uncentered payloads
and fine atoms need one extra source column only when the leaf is unfinished. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

theorem split_value_eq_retained {n r s : ℕ} {τ : ℝ} (f : Latent n → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hsource : ∀ z : Latent n,(∀ k : Fin (n+1),r≤k.val → |z.snd k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → (gradient f z).fst k=0)
    (htarget : ∀ z : Latent n,(∀ k : Fin (n+1),r≤k.val → |z.snd k|≤τ) →
      ∀ k : Fin (n+1),r≤k.val → (gradient f z).snd k=0)
    (z : Latent n) (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤τ) :
    f z=f (pack (retain n s z.fst) (retain n r z.snd)) := by
  have hsmooth (b : Space n) : ContDiff ℝ 3 (fun a : Space n => f (pack a b)) :=
    hf.comp ((packLinear (X:=Space n) (Y:=Space n)).contDiff.comp (contDiff_id.prodMk contDiff_const))
  have htsmooth (a : Space n) : ContDiff ℝ 3 (fun b : Space n => f (pack a b)) :=
    hf.comp ((packLinear (X:=Space n) (Y:=Space n)).contDiff.comp (contDiff_const.prodMk contDiff_id))
  have hs : f z=f (pack (retain n s z.fst) z.snd) := by
    apply value_eq_retain (r:=n+1) (s:=s) (τ:=0) (fun a => f (pack a z.snd))
      ((hsmooth z.snd).differentiable (by norm_num))
    · intro a _ k hk
      have he : gradient (fun u => f (pack u z.snd)) a=(gradient f (pack a z.snd)).fst :=
        (partial_x ((hf.differentiable (by norm_num) (pack a z.snd)).hasGradientAt)).gradient
      rw [he]
      exact hsource (pack a z.snd) hz k hk
    · intro k hk
      have := k.isLt
      omega
  apply hs.trans
  apply value_eq_retain (r:=r) (s:=r) (τ:=τ) (fun b => f (pack (retain n s z.fst) b))
    ((htsmooth _).differentiable (by norm_num))
  · intro b hb k hk
    have he : gradient (fun u => f (pack (retain n s z.fst) u)) b=
        (gradient f (pack (retain n s z.fst) b)).snd :=
      (partial_y ((hf.differentiable (by norm_num) (pack (retain n s z.fst) b)).hasGradientAt)).gradient
    rw [he]
    exact htarget (pack (retain n s z.fst) b) hb k hk
  · exact hz

theorem centeredPayload_flexible_prefix (n r s : ℕ) (hrs : r≤s)
    (ell h A ν g hp T : ℝ) (hh : 0<h) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤3*h/16) :
    centeredPayload n ell h A ν g hp T z=
      centeredPayload n ell h A ν g hp T (pack (retain n s z.fst) (retain n r z.snd)) := by
  apply split_value_eq_retained _ (centeredPayload_contDiff n ell h A ν g hp T) _ _ z hz
  · intro w hw k hk
    exact (centeredPayload_gradient_support n r ell h A ν g hp T hh w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith))).1 k (hrs.trans hk)
  · intro w hw k hk
    exact (centeredPayload_gradient_support n r ell h A ν g hp T hh w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith))).2 k hk

theorem payload_flexible_prefix (n r s : ℕ) (hrs : r≤s) (hnext : r≤n → r<s)
    (ell h A ν g hp T : ℝ) (hh : 0<h) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤3*h/16) :
    payload n ell h A ν g hp T z=
      payload n ell h A ν g hp T (pack (retain n s z.fst) (retain n r z.snd)) := by
  apply split_value_eq_retained _ (payload_contDiff n 3 ell h A ν g hp T) _ _ z hz
  · intro w hw k hk
    have hrn : r≤n := by have := k.isLt;omega
    exact (ChiSplitFine.payload_gradient_support n r ell h A ν g hp T hh w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith))).1 k (by have := hnext hrn;omega)
  · intro w hw k hk
    exact (ChiSplitFine.payload_gradient_support n r ell h A ν g hp T hh w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith))).2 k hk

end Bilevel.ChiSplitChain
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

theorem pieces_flexible_prefix (P : ChiFine.Parameters) (n p r s : ℕ)
    (hrs : r≤s) (hnext : r≤n → r<s) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤3*P.β/16) :
    pieces P n p z=pieces P n p (pack (retain n s z.fst) (retain n r z.snd)) := by
  apply ChiSplitChain.split_value_eq_retained _ (pieces_contDiff P n p) _ _ z hz
  · intro w hw k hk
    have hrn : r≤n := by have := k.isLt;omega
    exact (pieces_gradient_support P n p r w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith [P.β_pos]))).1 k (by have := hnext hrn;omega)
  · intro w hw k hk
    exact (pieces_gradient_support P n p r w
      (fun a ha => lt_of_le_of_lt (hw a ha) (by linarith [P.β_pos]))).2 k hk

end Bilevel.ChiSplitFine
