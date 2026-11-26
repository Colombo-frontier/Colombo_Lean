import RationalCompactMaster254

namespace Paper254

/-- Rational-cell ownership for the cached scalar Taylor recurrence. -/
def profiledTaylorState (x : ℚ) : ℕ→(ℚ×ℚ×ℕ)×ℕ
  | 0=>((1,0,0),2)
  | n+1=>
    let prev:=profiledTaylorState x n
    ((prev.1.1*x/(n+1),prev.1.2.1+prev.1.1,prev.1.2.2+3),max (prev.2+1) 6)

theorem profiledTaylorState_program (x : ℚ) (n : ℕ) :
    (profiledTaylorState x n).1=countedTaylorState x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [profiledTaylorState,ih,countedTaylorState]

theorem profiledTaylorState_workspace (x : ℚ) (n : ℕ) :
    (profiledTaylorState x n).2≤n+6 := by
  induction n with
  | zero => simp [profiledTaylorState]
  | succ n ih => simp only [profiledTaylorState,max_le_iff]; omega

def profiledRationalExp (x : ℚ) (p : ℕ) : (ℚ×ℕ)×ℕ :=
  let out:=profiledTaylorState x (p+3)
  ((out.1.2.1,out.1.2.2),out.2)

theorem profiledRationalExp_program (x : ℚ) (p : ℕ) :
    (profiledRationalExp x p).1=countedRationalExp x p := by
  simp only [profiledRationalExp,profiledTaylorState_program,countedRationalExp]

theorem profiledRationalExp_workspace (x : ℚ) (p : ℕ) :
    (profiledRationalExp x p).2≤p+9 := by
  exact (profiledTaylorState_workspace x (p+3)).trans (by omega)

def profiledRatPow (a : ℚ) : ℕ→(ℚ×ℕ)×ℕ
  | 0=>((1,0),1)
  | n+1=>
    let prev:=profiledRatPow a n
    ((prev.1.1*a,prev.1.2+1),max (prev.2+1) 3)

theorem profiledRatPow_program (a : ℚ) (n : ℕ) :
    (profiledRatPow a n).1=countedRatPow a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [profiledRatPow,ih,countedRatPow]

theorem profiledRatPow_workspace (a : ℚ) (n : ℕ) :
    (profiledRatPow a n).2≤n+3 := by
  induction n with
  | zero => simp [profiledRatPow]
  | succ n ih => simp only [profiledRatPow,max_le_iff]; omega

/-- The head result remains owned while the tail is evaluated, exactly
as in mapWithCosts. Caller-owned input cells are accounted outside. -/
def profiledMasterMap {α β : Type} (outputCells : ℕ) (f : α→(β×ℕ)×ℕ) :
    List α→(List β×ℕ)×ℕ
  | []=>(([],0),0)
  | x::xs=>let head:=f x; let tail:=profiledMasterMap outputCells f xs
            ((head.1.1::tail.1.1,head.1.2+tail.1.2),
              max (head.2+outputCells) (outputCells+tail.2))

theorem profiledMasterMap_program {α β : Type} (outputCells : ℕ)
    (f : α→(β×ℕ)×ℕ) (xs : List α) :
    (profiledMasterMap outputCells f xs).1=mapWithCosts (fun x=>(f x).1) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [profiledMasterMap,ih,mapWithCosts]

theorem profiledMasterMap_workspace {α β : Type} (outputCells : ℕ)
    (f : α→(β×ℕ)×ℕ) (xs : List α) (B : ℕ) (hB : ∀ x∈xs,(f x).2≤B) :
    (profiledMasterMap outputCells f xs).2≤xs.length*outputCells+B := by
  induction xs with
  | nil => simp [profiledMasterMap]
  | cons x xs ih =>
    have hh:=hB x (by simp)
    have ht:=ih (fun y hy=>hB y (by simp [hy]))
    simp only [profiledMasterMap,max_le_iff,List.length_cons]
    constructor <;> nlinarith

def profiledRationalSum : List ℚ→(ℚ×ℕ)×ℕ
  | []=>((0,0),1)
  | x::xs=>
    let tail:=profiledRationalSum xs
    ((x+tail.1.1,tail.1.2+1),max (tail.2+1) 3)

theorem profiledRationalSum_program (xs : List ℚ) :
    (profiledRationalSum xs).1=countedRationalSum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [profiledRationalSum,ih,countedRationalSum]

theorem profiledRationalSum_workspace (xs : List ℚ) :
    (profiledRationalSum xs).2≤xs.length+3 := by
  induction xs with
  | nil => simp [profiledRationalSum]
  | cons x xs ih => simp only [profiledRationalSum,max_le_iff,List.length_cons]; omega

def profiledNormalize {n : ℕ} (entries : List (Fin n×ℚ)) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let total:=profiledRationalSum (entries.map Prod.snd)
  let out:=profiledMasterMap 1 (fun e=>(((e.1,e.2/total.1.1),1),2)) entries
  ((out.1.1,total.1.2+out.1.2),
    max (entries.length+total.2) (entries.length+1+out.2))

theorem profiledNormalize_program {n : ℕ} (entries : List (Fin n×ℚ)) :
    (profiledNormalize entries).1=countedNormalize entries := by
  simp only [profiledNormalize,profiledRationalSum_program,profiledMasterMap_program,countedNormalize]

theorem profiledNormalize_workspace {n : ℕ} (entries : List (Fin n×ℚ)) :
    (profiledNormalize entries).2≤2*entries.length+3 := by
  have ht:=profiledRationalSum_workspace (entries.map Prod.snd)
  have ho:=profiledMasterMap_workspace 1
    (fun e : Fin n×ℚ=>(((e.1,e.2/(profiledRationalSum (entries.map Prod.snd)).1.1),1),2))
    entries 2 (by intros; rfl)
  simp only [List.length_map] at ht
  simp only [profiledNormalize,max_le_iff]
  constructor <;> omega

def profiledLiveSoftmax {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=profiledMasterMap 1 (fun e=>
    let exponential:=profiledRationalExp (z e) (p+4)
    (((e,w e*exponential.1.1),exponential.1.2+1),exponential.2+2)) (live.sort (·≤·))
  let normalized:=profiledNormalize raw.1.1
  let power:=profiledRatPow 2 p
  let bump : ℚ×ℕ := (3/(2*power.1.1),2)
  let upper:=profiledMasterMap 1 (fun e=>
    (((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1),p+8)) normalized.1.1
  let out:=profiledNormalize upper.1.1
  ((out.1.1,raw.1.2+normalized.1.2+power.1.2+bump.2+upper.1.2+out.1.2),
    max raw.2 (max (raw.1.1.length+normalized.2)
      (max (normalized.1.1.length+power.2+2)
        (max (normalized.1.1.length+upper.2+2) (upper.1.1.length+out.2)))))

theorem profiledLiveSoftmax_program {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) :
    (profiledLiveSoftmax p roundCost live w z).1=countedLiveSoftmax p roundCost live w z := by
  simp only [profiledLiveSoftmax,profiledNormalize_program,profiledMasterMap_program,
    profiledRationalExp_program,profiledRatPow_program,countedLiveSoftmax]

theorem profiledLiveSoftmax_workspace {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) :
    (profiledLiveSoftmax p roundCost live w z).2≤4*live.card+2*p+20 := by
  let raw:=profiledMasterMap 1 (fun e=>
    let exponential:=profiledRationalExp (z e) (p+4)
    (((e,w e*exponential.1.1),exponential.1.2+1),exponential.2+2)) (live.sort (·≤·))
  let normalized:=profiledNormalize raw.1.1
  let power:=profiledRatPow 2 p
  let bump : ℚ×ℕ := (3/(2*power.1.1),2)
  let upper:=profiledMasterMap 1 (fun e=>
    (((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1),p+8)) normalized.1.1
  have hr : raw.2≤live.card+p+15 := by
    have hh:=profiledMasterMap_workspace 1 (fun e=>
      let exponential:=profiledRationalExp (z e) (p+4)
      (((e,w e*exponential.1.1),exponential.1.2+1),exponential.2+2)) (live.sort (·≤·)) (p+15) (by
      intro e he
      have ht:=profiledRationalExp_workspace (z e) (p+4)
      dsimp only; omega)
    simpa only [raw,Finset.length_sort,Nat.mul_one,Nat.add_assoc] using hh
  have hrl : raw.1.1.length=live.card := by
    simp only [raw,profiledMasterMap_program,mapWithCosts_length,Finset.length_sort]
  have hnl : normalized.1.1.length=live.card := by
    dsimp only [normalized]
    rw [profiledNormalize_program,countedNormalize_length,hrl]
  have hul : upper.1.1.length=live.card := by
    dsimp only [upper]
    rw [profiledMasterMap_program,mapWithCosts_length,hnl]
  have hn:=profiledNormalize_workspace raw.1.1
  rw [hrl] at hn
  have hu : upper.2≤live.card+p+8 := by
    have hh:=profiledMasterMap_workspace 1 (fun e : Fin n×ℚ=>
      (((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1),p+8)) normalized.1.1 (p+8) (by intros; rfl)
    simpa only [upper,hnl,Nat.mul_one,Nat.add_assoc] using hh
  have ho:=profiledNormalize_workspace upper.1.1
  rw [hul] at ho
  have hp:=profiledRatPow_workspace 2 p
  change normalized.2≤2*live.card+3 at hn
  change max raw.2 (max (raw.1.1.length+normalized.2)
    (max (normalized.1.1.length+power.2+2)
      (max (normalized.1.1.length+upper.2+2)
        (upper.1.1.length+(profiledNormalize upper.1.1).2))))≤_
  rw [hrl,hnl,hul]
  simp only [max_le_iff]
  dsimp [power] at *
  omega

def profiledPruneShare {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=profiledMasterMap 1 (fun e=>(((e,(1-alpha)*w e+alpha*prior e),4),5)) (next.sort (·≤·))
  let out:=profiledNormalize raw.1.1
  ((out.1.1,raw.1.2+out.1.2),max raw.2 (raw.1.1.length+out.2))

theorem profiledPruneShare_program {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    (profiledPruneShare w prior alpha next).1=countedPruneShare w prior alpha next := by
  simp only [profiledPruneShare,profiledMasterMap_program,profiledNormalize_program,countedPruneShare]

theorem profiledPruneShare_workspace {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    (profiledPruneShare w prior alpha next).2≤3*next.card+5 := by
  let raw:=profiledMasterMap 1 (fun e=>(((e,(1-alpha)*w e+alpha*prior e),4),5)) (next.sort (·≤·))
  have hr : raw.2≤next.card+5 := by
    have hh:=profiledMasterMap_workspace 1
      (fun e=>(((e,(1-alpha)*w e+alpha*prior e),4),5)) (next.sort (·≤·)) 5 (by intros; rfl)
    simpa only [raw,Finset.length_sort,Nat.mul_one] using hh
  have hl : raw.1.1.length=next.card := by
    simp only [raw,profiledMasterMap_program,mapWithCosts_length,Finset.length_sort]
  have ho:=profiledNormalize_workspace raw.1.1
  rw [hl] at ho
  change max raw.2 (raw.1.1.length+(profiledNormalize raw.1.1).2)≤_
  rw [hl,max_le_iff]
  constructor <;> omega

def profiledMasterUpdate {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let weighted:=profiledLiveSoftmax p roundCost live w z
  let shared:=profiledPruneShare (rationalLookup weighted.1.1) prior alpha next
  let out:=profiledLiveSoftmax p roundCost next (rationalLookup shared.1.1) (fun _=>0)
  ((out.1.1,weighted.1.2+shared.1.2+out.1.2),
    max weighted.2 (max (weighted.1.1.length+shared.2) (shared.1.1.length+out.2)))

theorem profiledMasterUpdate_program {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) :
    (profiledMasterUpdate p roundCost live next w z prior alpha).1=
      countedMasterUpdate p roundCost live next w z prior alpha := by
  simp only [profiledMasterUpdate,profiledLiveSoftmax_program,profiledPruneShare_program,countedMasterUpdate]

theorem profiledMasterUpdate_workspace {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) :
    (profiledMasterUpdate p roundCost live next w z prior alpha).2≤24*(live.card+next.card+p+1) := by
  let weighted:=profiledLiveSoftmax p roundCost live w z
  let shared:=profiledPruneShare (rationalLookup weighted.1.1) prior alpha next
  have hw:=profiledLiveSoftmax_workspace p roundCost live w z
  have hs:=profiledPruneShare_workspace (rationalLookup weighted.1.1) prior alpha next
  have ho:=profiledLiveSoftmax_workspace p roundCost next (rationalLookup shared.1.1) (fun _=>0)
  have hwl : weighted.1.1.length=live.card := by
    dsimp only [weighted]
    rw [profiledLiveSoftmax_program,countedLiveSoftmax_length]
  have hsl : shared.1.1.length=next.card := by
    dsimp only [shared]
    rw [profiledPruneShare_program]
    simp only [countedPruneShare,countedNormalize_length,mapWithCosts_length,Finset.length_sort]
  change max weighted.2 (max (weighted.1.1.length+shared.2)
    (shared.1.1.length+(profiledLiveSoftmax p roundCost next (rationalLookup shared.1.1) (fun _=>0)).2))≤_
  rw [hwl,hsl]
  simp only [max_le_iff]
  change weighted.2≤4*live.card+2*p+20 at hw
  change shared.2≤3*next.card+5 at hs
  omega

end Paper254
#print axioms Paper254.profiledMasterUpdate_program
#print axioms Paper254.profiledMasterUpdate_workspace
