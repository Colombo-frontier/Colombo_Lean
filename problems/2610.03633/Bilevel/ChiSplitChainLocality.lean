import Bilevel.ChiSplitChain

/-! Exact off-graph source/predecessor support of the split chain. Smallness
is imposed only on the predecessor tail; source coordinates are unrestricted. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ZeroChainPotential PrimitiveGeometry

theorem sourceGradient_apply (n : ℕ) (z : Latent n) (j : Fin (n+1)) :
    sourceGradient n z j=(if j=0 then -phiSlope (z.fst 0) else 0)+
      ∑ i : Fin n,if j=i.succ then edgeRight (z.snd i.castSucc) (z.fst i.succ) else 0 := by
  have hs : (∑ i : Fin n,edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ) j=
      ∑ i : Fin n,(edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ) j := map_sum (EuclideanSpace.proj (𝕜:=ℝ) j)
    (fun i : Fin n => edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ) Finset.univ
  change (-phiSlope (z.fst 0))*(basis (0:Fin (n+1)) j)+
    (∑ i : Fin n,edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ) j= _
  rw [hs]
  simp [basis,smul_eq_mul,mul_ite]

theorem targetGradient_apply (n : ℕ) (z : Latent n) (j : Fin (n+1)) :
    targetGradient n z j=∑ i : Fin n,if j=i.castSucc then edgeLeft (z.snd i.castSucc) (z.fst i.succ) else 0 := by
  have hs : (∑ i : Fin n,edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc) j=
      ∑ i : Fin n,(edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc) j := map_sum (EuclideanSpace.proj (𝕜:=ℝ) j)
    (fun i : Fin n => edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc) Finset.univ
  change (∑ i : Fin n,edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc) j= _
  rw [hs]
  simp [basis,smul_eq_mul,mul_ite]

theorem sourceGradient_first (n : ℕ) (z : Latent n) : sourceGradient n z 0= -phiSlope (z.fst 0) := by
  rw [sourceGradient_apply]
  simp [eq_comm,Fin.succ_ne_zero]

theorem sourceGradient_succ {n : ℕ} (z : Latent n) (j : Fin n) :
    sourceGradient n z j.succ=edgeRight (z.snd j.castSucc) (z.fst j.succ) := by
  rw [sourceGradient_apply]
  simp [Fin.succ_inj,eq_comm]

theorem sourceGradient_support {n : ℕ} (r : ℕ) (z : Latent n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : sourceGradient n z j=0 := by
  revert hj
  refine Fin.cases (by simp) (fun i hi => ?_) j
  rw [sourceGradient_succ]
  exact edgeRight_inactive _ _ (by have hh := hz i.castSucc (by simpa using Nat.le_of_succ_le_succ hi); linarith)

theorem targetGradient_support {n : ℕ} (r : ℕ) (z : Latent n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) : targetGradient n z j=0 := by
  rw [targetGradient_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with he
  · exact edgeLeft_inactive _ _ (by have hh := hz j hj; rw [he] at hh; linarith)
  · rfl

theorem actual_gradient_support {n : ℕ} (r : ℕ) (z : Latent n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4) :
    (∀ j : Fin (n+1),r+1≤j.val → (gradient (value n) z).fst j=0) ∧
    (∀ j : Fin (n+1),r≤j.val → (gradient (value n) z).snd j=0) := by
  rw [actual_gradient]
  exact ⟨fun j hj => sourceGradient_support r z hz j hj,fun j hj => targetGradient_support r z hz j hj⟩

def frontierSourceGradient (n : ℕ) (a b : Space n) : Space n :=
  ∑ i : Fin (n+1),(-selector n i b*phiSlope (a i)) • basis i

theorem frontier_source_hasGradientAt (n : ℕ) (a b : Space n) :
    HasGradientAt (fun u => frontier n (pack u b)) (frontierSourceGradient n a b) a := by
  have ht (i : Fin (n+1)) :=
    (((phi_hasDerivAt (a i)).hasFDerivAt.comp a (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt).sub_const (phi 0)).const_mul
      (-selector n i b)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert HasFDerivAt.sum (fun i (_ : i∈Finset.univ) => ht i) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,frontierSourceGradient,sum_inner,real_inner_smul_left,inner_basis,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (-selector n i b*phiSlope (a i))*v i= -selector n i b*(v i*phiSlope (a i))
  ring

theorem frontierSourceGradient_apply (n : ℕ) (a b : Space n) (j : Fin (n+1)) :
    frontierSourceGradient n a b j= -selector n j b*phiSlope (a j) := by
  have hs : (∑ i : Fin (n+1),(-selector n i b*phiSlope (a i)) • basis i) j=
      ∑ i : Fin (n+1),((-selector n i b*phiSlope (a i)) • basis i) j := map_sum (EuclideanSpace.proj (𝕜:=ℝ) j)
    (fun i : Fin (n+1) => (-selector n i b*phiSlope (a i)) • basis i) Finset.univ
  change (∑ i : Fin (n+1),(-selector n i b*phiSlope (a i)) • basis i) j= _
  rw [hs]
  simp [basis,smul_eq_mul,mul_ite]

theorem sourceGradient_frontier_tail {n : ℕ} (r : ℕ) (z : Latent n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) :
    sourceGradient n z j=frontierSourceGradient n z.fst z.snd j := by
  have hm : tailMask j z.snd=1 := tailMask_one_of_small j z.snd (fun i hi => hz i (hj.trans hi))
  rw [frontierSourceGradient_apply]
  revert hm
  refine Fin.cases ?_ (fun i hh => ?_) j
  · intro hh
    rw [sourceGradient_first]
    simp [selector,hh]
  · rw [sourceGradient_succ]
    simp only [selector,Fin.cases_succ,hh,mul_one,edgeRight,phiSlope_even,evenGate]
    ring

theorem carrier_source_gradient_support {n : ℕ} (r : ℕ) (a b : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |b j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (fun u => carrier n (pack u b)) a j=0 := by
  have hs := PrimitiveGeometry.partial_x (value_hasGradientAt n (pack a b))
  have hf := frontier_source_hasGradientAt n a b
  have hd : HasGradientAt (fun u => carrier n (pack u b))
      (sourceGradient n (pack a b)-frontierSourceGradient n a b) a := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [carrier,map_sub] using hs.hasFDerivAt.sub hf.hasFDerivAt
  rw [hd.gradient]
  change sourceGradient n (pack a b) j-frontierSourceGradient n a b j=0
  exact sub_eq_zero.mpr (sourceGradient_frontier_tail r (pack a b) hz j hj)

end Bilevel.ChiSplitChain
