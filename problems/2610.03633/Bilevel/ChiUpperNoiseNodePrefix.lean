import Bilevel.ChiVirtualNodeValues
import Bilevel.ChiFineInactiveLocality

/-! Direct upper-noise leaves: an active payload needs only the prospective
column; subtracting its fixed signal leaves an old-prefix scalar. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive

theorem direct_payload_value_eq_retain (n r s : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h)
    (hrs : r≤s) (hnext : n<r ∨ r<s) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤h/4) :
    payload n ell h A ν g hp T z=payload n ell h A ν g hp T (retain n s z) := by
  apply value_eq_retain _ ((payload_contDiff n ell h A ν g hp T 3).differentiable (by norm_num)) _ z hz
  intro w hw k hk
  rcases hnext with hn|hn
  · have := k.isLt
    omega
  · have ha := centeredPayload_gradient_support n r ell h A ν g hp T hh w hw k (by omega)
    rw [ChiFine.gradient_sub_C3 (payload_contDiff n ell h A ν g hp T 3)
      (ChiFine.frontier_contDiff n ell h),PiLp.sub_apply] at ha
    have hb : gradient (ChiFine.frontier n ell h) w k=0 :=
      Rcentered_gradient_support n r ell h hh w hw k (by omega)
    linarith

theorem direct_inactive_payload_value_eq_retain (n r : ℕ) (ell h A ν g hp T τ : ℝ)
    (hh : 0<h) (hτ : 0<τ) (hτh : τ≤h/16) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ) :
    payload n ell h A ν g hp T z-ChiFine.frontier n ell h z+ChiFine.flatFrontier n ell h τ z=
      payload n ell h A ν g hp T (retain n r z)-ChiFine.frontier n ell h (retain n r z)+
        ChiFine.flatFrontier n ell h τ (retain n r z) := by
  have hc := centeredPayload_prefix_value n r ell h A ν g hp T hh z (fun k hk => by
    have hb := hz k hk
    linarith)
  have hf := value_eq_retain (ChiFine.flatFrontier n ell h τ)
    ((ChiFine.flatFrontier_contDiff n ell h τ).differentiable (by norm_num))
    (fun w hw k hk => ChiFine.inactive_gradient_support n r ell h τ hh hτ hτh w hw k hk) z hz
  rw [hc,hf]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_direct_payload_eq_virtual (N : Node E) (r s : ℕ) (columns : Fin (N.n+1) → E)
    (hp : ∀ k : Fin (N.n+1),k.val<s → columns k=N.frame (basis k))
    (hh : 0<N.width) (hrs : r≤s) (hnext : N.n<r ∨ r<s) (u : E)
    (hz : ∀ k : Fin (N.n+1),r≤k.val → |N.coordinates u k|≤N.width/4) :
    N.H u=virtualH N s columns u := by
  unfold Node.H virtualH
  rw [readout_eq_retained N.n s N.radius columns N.frame hp]
  exact direct_payload_value_eq_retain N.n r s N.ell N.width N.receiver N.nu N.force N.parentWidth
    N.tailRadius hh hrs hnext (N.coordinates u) hz

end Bilevel.ChiPrefixEvaluation

