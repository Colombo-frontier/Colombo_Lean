import Bilevel.ChiFinePrefixLocality
import Bilevel.ChiFineSignalCore

/-! Exact latent support of every fixed inactive fine atom, including the
single-atom schedule. The last incoming frontier is cancelled algebraically;
all remaining profiles are flat on the finest inactive interval. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain

theorem gradient_sub_C3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (z : E) :
    gradient (fun x => f x-g x) z=gradient f z-gradient g z := by
  have hh : HasGradientAt (fun x => f x-g x) (gradient f z-gradient g z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sub] using
      ((hf.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt).sub
        ((hg.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  exact hh.gradient

def inactiveAtom (n J : ℕ) (δ : ℕ → ℝ) (τ : ℝ) (k : ℕ) : Space n → ℝ :=
  if k=J then fun z => piece n J δ k z-(centeredResidual n z-flattened n τ z) else piece n J δ k

theorem inactiveAtom_contDiff (n J : ℕ) (δ : ℕ → ℝ) (τ : ℝ) (k : ℕ) :
    ContDiff ℝ 3 (inactiveAtom n J δ τ k) := by
  unfold inactiveAtom
  split_ifs
  · exact (piece_contDiff n J δ k).sub ((centeredResidual_contDiff n 3).sub (flattened_contDiff n τ))
  · exact piece_contDiff n J δ k

theorem inactiveAtom_single (n : ℕ) (δ : ℕ → ℝ) (τ : ℝ) :
    inactiveAtom n 0 δ τ 0=flattened n τ := by
  funext z
  simp only [inactiveAtom,if_pos rfl,piece,approximation,lt_self_iff_false,if_false,if_true]
  ring

theorem inactiveAtom_last (n J : ℕ) (δ : ℕ → ℝ) (τ : ℝ) :
    inactiveAtom n (J+1) δ τ (J+1)=fun z => flattened n τ z-flattened n (δ J) z := by
  funext z
  simp only [inactiveAtom,if_pos rfl,piece,approximation,lt_self_iff_false,if_false,
    Nat.lt_succ_self,if_true]
  ring

theorem inactiveAtom_gradient_small (n J : ℕ) (δ : ℕ → ℝ) (τ : ℝ)
    (hτ : 0<τ) (hsτ : τ≤1/16) (hpos : ∀ k,k<J → 0<δ k)
    (hs : ∀ k,k<J → δ k≤1/16) (hτδ : ∀ k,k<J → τ≤δ k)
    (k : ℕ) (hk : k≤J) (z : Space n) (j : Fin (n+1)) (hj : |z j|≤τ) :
    gradient (inactiveAtom n J δ τ k) z j=0 := by
  have hflat (l : ℕ) (hl : l<J) : gradient (flattened n (δ l)) z j=0 :=
    flattened_gradient_small (δ l) (hpos l hl) (hs l hl) z j (hj.trans (hτδ l hl))
  have hflatτ := flattened_gradient_small τ hτ hsτ z j hj
  by_cases he : k=J
  · subst k
    cases J with
    | zero => rw [inactiveAtom_single];exact hflatτ
    | succ J =>
      rw [inactiveAtom_last,gradient_sub_C3 (flattened_contDiff n τ) (flattened_contDiff n (δ J)),PiLp.sub_apply,
        hflatτ,hflat J (Nat.lt_succ_self _),sub_self]
  · have hkJ : k<J := lt_of_le_of_ne hk he
    rw [inactiveAtom,if_neg he]
    cases k with
    | zero =>
      rw [show piece n J δ 0=flattened n (δ 0) by funext x;simp [piece,approximation,hkJ]]
      exact hflat 0 hkJ
    | succ k =>
      have heq : piece n J δ (k+1)=fun x => flattened n (δ (k+1)) x-flattened n (δ k) x := by
        funext x
        simp only [piece,approximation,if_pos hkJ,if_pos (show k<J by omega)]
      rw [heq,gradient_sub_C3 (flattened_contDiff n (δ (k+1))) (flattened_contDiff n (δ k)),PiLp.sub_apply,
        hflat (k+1) hkJ,hflat k (by omega),sub_self]

end Bilevel.ChiFine
