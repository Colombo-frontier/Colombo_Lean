import Bilevel.ChiBoundedChainReceiverShapeBounds

/-! Exact scaled derivatives of the actual receiver primitives. -/
noncomputable section
namespace Bilevel.ChiBoundedChain.ReceiverJets

theorem positiveSlope_normalization (A ν g h hp : ℝ) (hg : g≠0) (hh : h≠0) (hhp : hp≠0) :
    positiveReceiverSlope A ν g h hp=(fun t => -A*g*positiveShape (ν*h/g) (h/hp) (t/h)) := by
  funext t
  unfold positiveReceiverSlope positiveShape profile
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have he : h/hp*(t/h)=t/hp := by field_simp;ring
  rw [he]
  field_simp
  ring

theorem negativeSlope_normalization (A g h T : ℝ) (hh : h≠0) (hT : T≠0) :
    negativeReceiverSlope A g h T=(fun t => -A*g*negativeShape (h/T) (-t/h)) := by
  funext t
  unfold negativeReceiverSlope negativeShape profile
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val_two]
  have he : h/T*(-t/h)=-t/T := by field_simp;ring
  rw [he]
  change -A*g*receiverGate (-t/h)*negativeTail (-t/T)=
    -A*g*(receiverGate (-t/h)*negativeTail (-t/T))
  ring

theorem positiveSlope_hasDerivAt (A ν g h hp t : ℝ) (hg : g≠0) (hh : h≠0) (hhp : hp≠0) :
    HasDerivAt (positiveReceiverSlope A ν g h hp)
      ((-A*g/h)*positiveShapeFirst (ν*h/g) (h/hp) (t/h)) t := by
  rw [positiveSlope_normalization A ν g h hp hg hh hhp]
  convert ((positiveShape_hasDerivAt (ν*h/g) (h/hp) (t/h)).comp t
    ((hasDerivAt_id t).div_const h)).const_mul (-A*g) using 1
  ring

theorem negativeSlope_hasDerivAt (A g h T t : ℝ) (hh : h≠0) (hT : T≠0) :
    HasDerivAt (negativeReceiverSlope A g h T)
      ((A*g/h)*negativeShapeFirst (h/T) (-t/h)) t := by
  rw [negativeSlope_normalization A g h T hh hT]
  convert ((negativeShape_hasDerivAt (h/T) (-t/h)).comp t
    ((hasDerivAt_id t).neg.div_const h)).const_mul (-A*g) using 1
  ring

theorem positiveSlope_deriv_hasDerivAt (A ν g h hp t : ℝ) (hg : g≠0) (hh : h≠0) (hhp : hp≠0) :
    HasDerivAt (deriv (positiveReceiverSlope A ν g h hp))
      ((-A*g/h^2)*positiveShapeSecond (ν*h/g) (h/hp) (t/h)) t := by
  have he : deriv (positiveReceiverSlope A ν g h hp)=
      (fun s => (-A*g/h)*positiveShapeFirst (ν*h/g) (h/hp) (s/h)) :=
    funext (fun s => (positiveSlope_hasDerivAt A ν g h hp s hg hh hhp).deriv)
  rw [he]
  convert ((positiveShapeFirst_hasDerivAt (ν*h/g) (h/hp) (t/h)).comp t
    ((hasDerivAt_id t).div_const h)).const_mul (-A*g/h) using 1
  ring

theorem negativeSlope_deriv_hasDerivAt (A g h T t : ℝ) (hh : h≠0) (hT : T≠0) :
    HasDerivAt (deriv (negativeReceiverSlope A g h T))
      ((-A*g/h^2)*negativeShapeSecond (h/T) (-t/h)) t := by
  have he : deriv (negativeReceiverSlope A g h T)=
      (fun s => (A*g/h)*negativeShapeFirst (h/T) (-s/h)) :=
    funext (fun s => (negativeSlope_hasDerivAt A g h T s hh hT).deriv)
  rw [he]
  convert ((negativeShapeFirst_hasDerivAt (h/T) (-t/h)).comp t
    ((hasDerivAt_id t).neg.div_const h)).const_mul (A*g/h) using 1
  ring

theorem positiveReceiver_second (A ν g h hp t : ℝ) (hg : g≠0) (hh : h≠0) (hhp : hp≠0) :
    iteratedDeriv 2 (positiveReceiver A ν g h hp) t=
      (-A*g/h)*positiveShapeFirst (ν*h/g) (h/hp) (t/h) := by
  have he : deriv (positiveReceiver A ν g h hp)=positiveReceiverSlope A ν g h hp :=
    funext (fun s => (positiveReceiver_hasDerivAt A ν g h hp s).deriv)
  rw [iteratedDeriv_succ',he,iteratedDeriv_one,(positiveSlope_hasDerivAt A ν g h hp t hg hh hhp).deriv]

theorem positiveReceiver_third (A ν g h hp t : ℝ) (hg : g≠0) (hh : h≠0) (hhp : hp≠0) :
    iteratedDeriv 3 (positiveReceiver A ν g h hp) t=
      (-A*g/h^2)*positiveShapeSecond (ν*h/g) (h/hp) (t/h) := by
  have he : deriv (positiveReceiver A ν g h hp)=positiveReceiverSlope A ν g h hp :=
    funext (fun s => (positiveReceiver_hasDerivAt A ν g h hp s).deriv)
  rw [iteratedDeriv_succ',he,iteratedDeriv_succ,iteratedDeriv_one,
    (positiveSlope_deriv_hasDerivAt A ν g h hp t hg hh hhp).deriv]

theorem negativeReceiver_second (A g h T t : ℝ) (hh : h≠0) (hT : T≠0) :
    iteratedDeriv 2 (negativeReceiver A g h T) t=
      (A*g/h)*negativeShapeFirst (h/T) (-t/h) := by
  have he : deriv (negativeReceiver A g h T)=negativeReceiverSlope A g h T :=
    funext (fun s => (negativeReceiver_hasDerivAt A g h T s).deriv)
  rw [iteratedDeriv_succ',he,iteratedDeriv_one,(negativeSlope_hasDerivAt A g h T t hh hT).deriv]

theorem negativeReceiver_third (A g h T t : ℝ) (hh : h≠0) (hT : T≠0) :
    iteratedDeriv 3 (negativeReceiver A g h T) t=
      (-A*g/h^2)*negativeShapeSecond (h/T) (-t/h) := by
  have he : deriv (negativeReceiver A g h T)=negativeReceiverSlope A g h T :=
    funext (fun s => (negativeReceiver_hasDerivAt A g h T s).deriv)
  rw [iteratedDeriv_succ',he,iteratedDeriv_succ,iteratedDeriv_one,
    (negativeSlope_deriv_hasDerivAt A g h T t hh hT).deriv]

end Bilevel.ChiBoundedChain.ReceiverJets
