import GradientHessian.DisclosureCompiler

/-! A literal, charged finite readout prelude. Countdown k synthesizes
readouts k-1,...,0 before entering the original preprocessing program. -/

noncomputable section
namespace GradientHessian.DisclosurePreload
open Classical Matrix MeasureTheory DisclosureCompiler

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

def program (P : Program d S) (mark : ℕ → S → Fin d → ℝ)
    (write : ℕ → S × (Fin d → ℝ) → S)
    (hm : ∀ k,Measurable (mark k)) (hw : ∀ k,Measurable (write k)) : Program d (S × ℕ) where
  mode := fun s => if s.2=0 then P.mode s.1 else 3
  think := fun s => (P.think s.1,s.2)
  query := fun s => P.query s.1
  mark := fun s => match s.2 with
    | 0 => P.mark s.1
    | k+1 => mark k s.1
  next := fun q => (P.next (q.1.1,q.2),q.1.2)
  disclosed := fun q => match q.1.2 with
    | 0 => (P.disclosed (q.1.1,q.2),0)
    | k+1 => (write k (q.1.1,q.2),k)
  mode_measurable := Measurable.ite (measurable_snd (measurableSet_singleton 0))
    (P.mode_measurable.comp measurable_fst) measurable_const
  think_measurable := (P.think_measurable.comp measurable_fst).prodMk measurable_snd
  query_measurable := P.query_measurable.comp measurable_fst
  mark_measurable := by
    apply measurable_from_prod_countable
    intro k
    cases k with
    | zero => exact P.mark_measurable
    | succ k => exact hm k
  next_measurable := (P.next_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)
  disclosed_measurable := by
    let f : (S × (Fin d → ℝ)) × ℕ → S × ℕ := fun q => match q.2 with
      | 0 => (P.disclosed q.1,0)
      | k+1 => (write k q.1,k)
    have hf : Measurable f := by
      apply measurable_from_prod_countable
      intro k
      cases k with
      | zero => exact P.disclosed_measurable.prodMk measurable_const
      | succ k => exact (hw k).prodMk measurable_const
    exact hf.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))

def prepared (mark : ℕ → S → Fin d → ℝ) (write : ℕ → S × (Fin d → ℝ) → S)
    (readout : (Fin d → ℝ) → Fin d → ℝ) : ℕ → S → S
  | 0,s => s
  | k+1,s => prepared mark write readout k (write k (s,readout (mark k s)))

variable (P : Program d S) (mark : ℕ → S → Fin d → ℝ)
  (write : ℕ → S × (Fin d → ℝ) → S)
  (hm : ∀ k,Measurable (mark k)) (hw : ∀ k,Measurable (write k))
  (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)

theorem eval_zero (N : ℕ) (s : S) :
    (program P mark write hm hw).eval A readout N (s,0)=
      ((P.eval A readout N s).1,(P.eval A readout N s).2,0) := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      by_cases h0 : P.mode s=0
      · simp [Program.eval,program,h0,Program.terminal,Program.flag]
      by_cases h1 : P.mode s=1
      · simpa only [Program.eval,program,if_true,h0,h1,if_false] using ih (P.think s)
      by_cases h2 : P.mode s=2
      · simpa only [Program.eval,program,if_true,h0,h1,h2,if_false] using ih (P.next (s,A*ᵥP.query s))
      · simpa only [Program.eval,program,if_true,h0,h1,h2,if_false] using ih (P.disclosed (s,readout (P.mark s)))

theorem calls_zero (N : ℕ) (s : S) :
    (program P mark write hm hw).ordinaryCalls A readout N (s,0)=P.ordinaryCalls A readout N s ∧
    (program P mark write hm hw).disclosures A readout N (s,0)=P.disclosures A readout N s := by
  induction N generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ N ih =>
      by_cases h0 : P.mode s=0
      · simp [Program.ordinaryCalls,Program.disclosures,program,h0]
      by_cases h1 : P.mode s=1
      · simpa only [Program.ordinaryCalls,Program.disclosures,program,if_true,h0,h1,if_false] using ih (P.think s)
      by_cases h2 : P.mode s=2
      · have hh := ih (P.next (s,A*ᵥP.query s))
        simpa only [Program.ordinaryCalls,Program.disclosures,program,if_true,h0,h1,h2,
          if_false,Fin.isValue,reduceCtorEq] using ⟨congrArg (fun x => x+1) hh.1,hh.2⟩
      · have hh := ih (P.disclosed (s,readout (P.mark s)))
        simpa only [Program.ordinaryCalls,Program.disclosures,program,if_true,h0,h1,h2,
          if_false,Fin.isValue,reduceCtorEq] using ⟨hh.1,congrArg (fun x => x+1) hh.2⟩

theorem eval_prepared (k N : ℕ) (s : S) :
    (program P mark write hm hw).eval A readout (k+N) (s,k)=
      ((P.eval A readout N (prepared mark write readout k s)).1,
        (P.eval A readout N (prepared mark write readout k s)).2,0) := by
  induction k generalizing s with
  | zero => simpa only [Nat.zero_add,prepared] using eval_zero P mark write hm hw A readout N s
  | succ k ih =>
      simpa only [Nat.succ_add,Program.eval,program,Nat.succ_ne_zero,if_false,
        Fin.isValue,reduceCtorEq,prepared] using ih (write k (s,readout (mark k s)))

theorem calls_prepared (k N : ℕ) (s : S) :
    (program P mark write hm hw).ordinaryCalls A readout (k+N) (s,k)=
      P.ordinaryCalls A readout N (prepared mark write readout k s) ∧
    (program P mark write hm hw).disclosures A readout (k+N) (s,k)=
      P.disclosures A readout N (prepared mark write readout k s)+k := by
  induction k generalizing s with
  | zero => simpa only [Nat.zero_add,prepared,Nat.add_zero] using calls_zero P mark write hm hw A readout N s
  | succ k ih =>
      have h := ih (write k (s,readout (mark k s)))
      simpa only [Nat.succ_add,Program.ordinaryCalls,Program.disclosures,program,Nat.succ_ne_zero,
        if_false,Fin.isValue,reduceCtorEq,prepared,Nat.add_succ,Nat.add_assoc] using
          (show (program P mark write hm hw).ordinaryCalls A readout (k+N)
              (write k (s,readout (mark k s)),k)=P.ordinaryCalls A readout N
                (prepared mark write readout k (write k (s,readout (mark k s)))) ∧
            (program P mark write hm hw).disclosures A readout (k+N)
              (write k (s,readout (mark k s)),k)+1=P.disclosures A readout N
                (prepared mark write readout k (write k (s,readout (mark k s))))+(k+1) from
                  ⟨h.1,by omega⟩)

end GradientHessian.DisclosurePreload
