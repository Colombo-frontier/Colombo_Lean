import ExactSparseCost254
import RationalCompactMaster254

noncomputable section
open scoped BigOperators
namespace Paper254

def realLookup {ι : Type} [DecidableEq ι] : List (ι×ℝ)→ι→ℝ
  | [],_=>0
  | (i,v)::xs,j=>if i=j then v else realLookup xs j

theorem realLookup_map {ι : Type} [DecidableEq ι] (xs : List ι) (f : ι→ℝ) (j : ι) :
    realLookup (xs.map (fun i=>(i,f i))) j=if j∈xs then f j else 0 := by
  induction xs with
  | nil => simp [realLookup]
  | cons i xs ih =>
    by_cases h : i=j
    · subst i; simp [realLookup]
    · simp [realLookup,h,ih,Ne.symm h]

theorem real_sum_toList {ι : Type} (s : Finset ι) (f : ι→ℝ) :
    (s.toList.map f).sum=∑ i∈s,f i := by
  change ((↑s.toList:Multiset ι).map f).sum=_
  rw [Finset.coe_toList]
  rfl

def countedRealSum : List ℝ→ℝ×ℕ
  | []=>(0,0)
  | x::xs=>let tail:=countedRealSum xs; (x+tail.1,tail.2+1)

theorem countedRealSum_spec (xs : List ℝ) : countedRealSum xs=(xs.sum,xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countedRealSum,ih]

def countedRealNormalize {ι : Type} (entries : List (ι×ℝ)) : List (ι×ℝ)×ℕ :=
  let total := countedRealSum (entries.map Prod.snd)
  let out := mapWithCosts (fun e=>((e.1,e.2/total.1),1)) entries
  (out.1,total.2+out.2)

theorem countedRealNormalize_value {ι : Type} (entries : List (ι×ℝ)) :
    (countedRealNormalize entries).1=entries.map (fun e=>(e.1,e.2/(entries.map Prod.snd).sum)) := by
  simp [countedRealNormalize,mapWithCosts_values,countedRealSum_spec]

theorem countedRealNormalize_cost {ι : Type} (entries : List (ι×ℝ)) :
    (countedRealNormalize entries).2=2*entries.length := by
  simp [countedRealNormalize,countedRealSum_spec,mapWithCosts_constant]
  omega

structure ExactExpPrimitive where
  run : ℝ→ℝ×ℕ
  value : ∀ x,(run x).1=Real.exp x
  bound : ℕ
  cost : ∀ x,(run x).2≤bound

def countedRealSoftmax {ι : Type} (exponential : ExactExpPrimitive)
    (live : Finset ι) (weights : ι→ℝ) (lam : ℝ) (loss : ι→ℝ×ℕ) : List (ι×ℝ)×ℕ :=
  let raw := mapWithCosts (fun e=>
    let ell := loss e
    let factor := exponential.run (-lam*ell.1)
    ((e,weights e*factor.1),ell.2+factor.2+3)) live.toList
  let out := countedRealNormalize raw.1
  (out.1,raw.2+out.2)

theorem countedRealSoftmax_value {ι : Type} [Fintype ι] [DecidableEq ι]
    (exponential : ExactExpPrimitive) (live : Finset ι) (weights : ι→ℝ)
    (lam : ℝ) (loss : ι→ℝ×ℕ) (hsupport : ∀ j,j∉live→weights j=0) :
    realLookup (countedRealSoftmax exponential live weights lam loss).1=
      exponentialUpdate lam weights (fun e=>(loss e).1) := by
  let f := fun e=>weights e*Real.exp (-lam*(loss e).1)
  have hsum : ∑ e∈live,f e=∑ e,f e := Finset.sum_subset (Finset.subset_univ _)
    (by intro e he hn; simp [f,hsupport e hn])
  funext j
  simp only [countedRealSoftmax,countedRealNormalize_value,mapWithCosts_values,
    exponential.value,List.map_map,Function.comp_def]
  change realLookup (live.toList.map (fun e=>(e,f e/(live.toList.map f).sum))) j=_
  rw [real_sum_toList,hsum,realLookup_map]
  by_cases hj : j∈live <;> simp [exponentialUpdate,exponentialNormalizer,f,hj,hsupport j]

theorem countedRealSoftmax_cost {ι : Type} (exponential : ExactExpPrimitive)
    (live : Finset ι) (weights : ι→ℝ) (lam : ℝ) (loss : ι→ℝ×ℕ)
    (C : ℕ) (hC : ∀ e∈live,(loss e).2≤C) :
    (countedRealSoftmax exponential live weights lam loss).2≤live.card*(C+exponential.bound+5) := by
  have hr := mapWithCosts_bound (fun e=>
    let ell := loss e
    let factor := exponential.run (-lam*ell.1)
    ((e,weights e*factor.1),ell.2+factor.2+3)) live.toList (C+exponential.bound+3) (by
      intro e he
      have hl := hC e (Finset.mem_toList.mp he)
      have hx := exponential.cost (-lam*(loss e).1)
      dsimp only; omega)
  simp only [countedRealSoftmax,countedRealNormalize_cost,mapWithCosts_length,Finset.length_toList]
  simp only [Finset.length_toList] at hr
  nlinarith

def countedRealPruneShare {ι : Type} (weights prior : ι→ℝ) (alpha : ℝ) (next : Finset ι) :
    List (ι×ℝ)×ℕ :=
  let raw := mapWithCosts (fun e=>((e,(1-alpha)*weights e+alpha*prior e),4)) next.toList
  let out := countedRealNormalize raw.1
  (out.1,raw.2+out.2)

theorem countedRealPruneShare_value {ι : Type} [Fintype ι] [DecidableEq ι]
    (p prior : ProbabilityWeights ι) (alpha : ℝ) (ha : 0<alpha) (hb : alpha≤1)
    (next : Finset ι) (hprior : ∀ j,0<prior.weight j→j∈next) :
    realLookup (countedRealPruneShare p.weight prior.weight alpha next).1=
      (p.pruneShare prior alpha ha hb next hprior).weight := by
  have hsum : ∑ e∈next,((1-alpha)*p.weight e+alpha*prior.weight e)=
      ∑ e,p.prunedMixtureMass prior alpha next e := by
    simp only [ProbabilityWeights.prunedMixtureMass,Finset.sum_ite_mem,Finset.univ_inter]
  funext j
  simp only [countedRealPruneShare,countedRealNormalize_value,mapWithCosts_values,
    List.map_map,Function.comp_def]
  rw [real_sum_toList,hsum,realLookup_map]
  by_cases hj : j∈next <;> simp [ProbabilityWeights.pruneShare,ProbabilityWeights.prunedMixtureMass,hj]

theorem countedRealPruneShare_cost {ι : Type} (weights prior : ι→ℝ) (alpha : ℝ) (next : Finset ι) :
    (countedRealPruneShare weights prior alpha next).2=6*next.card := by
  simp only [countedRealPruneShare,mapWithCosts_constant,countedRealNormalize_cost,
    mapWithCosts_length,Finset.length_toList]
  ring

def countedRealMaster {ι : Type} [DecidableEq ι] (exponential : ExactExpPrimitive)
    (live next : Finset ι) (weights prior : ι→ℝ) (lam alpha : ℝ) (loss : ι→ℝ×ℕ) : List (ι×ℝ)×ℕ :=
  let raw := countedRealSoftmax exponential live weights lam loss
  let out := countedRealPruneShare (realLookup raw.1) prior alpha next
  (out.1,raw.2+out.2)

theorem countedRealMaster_value {ι : Type} [Fintype ι] [DecidableEq ι]
    (exponential : ExactExpPrimitive) (live next : Finset ι) (p prior : ProbabilityWeights ι)
    (lam alpha : ℝ) (loss : ι→ℝ×ℕ) (ha : 0<alpha) (hb : alpha≤1)
    (hprior : ∀ j,0<prior.weight j→j∈next) (hsupport : ∀ j,j∉live→p.weight j=0) :
    realLookup (countedRealMaster exponential live next p.weight prior.weight lam alpha loss).1=
      ((p.exponential lam (fun e=>(loss e).1)).pruneShare prior alpha ha hb next hprior).weight := by
  dsimp only [countedRealMaster]
  rw [countedRealSoftmax_value _ _ _ _ _ hsupport]
  exact countedRealPruneShare_value (p.exponential lam (fun e=>(loss e).1)) prior alpha ha hb next hprior

theorem countedRealMaster_cost {ι : Type} [DecidableEq ι]
    (exponential : ExactExpPrimitive) (live next : Finset ι) (weights prior : ι→ℝ)
    (lam alpha : ℝ) (loss : ι→ℝ×ℕ) (C : ℕ) (hC : ∀ e∈live,(loss e).2≤C) :
    (countedRealMaster exponential live next weights prior lam alpha loss).2≤
      live.card*(C+exponential.bound+5)+6*next.card := by
  dsimp only [countedRealMaster]
  rw [countedRealPruneShare_cost]
  exact Nat.add_le_add_right (countedRealSoftmax_cost exponential live weights lam loss C hC) _

end Paper254
#print axioms Paper254.countedRealMaster_value
#print axioms Paper254.countedRealMaster_cost
