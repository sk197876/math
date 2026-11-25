(** Federer (1969), 4.1.24, p. 382: both
    original rectifiable series have actual sums in
    exactly R_(m,K), with every chosen coefficient
    retained in the literal numerical tail. Apply the
    proved same-K mass completeness and original weak
    mass lower semicontinuity. No normality of the
    summands is added. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed CurrentMassConvergenceUP
  CurrentWeakSequenceLimit CurrentWeakLimitOperations CurrentMassWeakLowerLimit
  CurrentMassIncrementTails CurrentMassCauchyTails
  NonnegativeSum NonnegativeSequenceTail NonnegativeRealSeriesTails
  RectifiableCurrentApproximationUP RectifiableCurrentFiniteSums RectifiableCurrentMassSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCurrentMassSeries.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).

(** Source for [rectifiable_current_mass_series_exists]: the
    actual original rectifiable series sum and every
    exact chosen mass-tail bound, 4.1.24, p. 382.
    All summands and the limit retain the original K. *)
Theorem rectifiable_current_mass_series_exists (v:nat->C) (a:nat->R):
  (forall k,Rect (v k))->(forall k,0<=a k)->
  (nonnegative_sum setT (fun k=>(a k)%:E)< +oo)%E->
  (forall k,(M (v k)<=(a k)%:E)%E)->
  exists S:C,Rect S /\
    @is_current_mass_sequence_limit R h2 n m U hU (fun k=>\sum_(j<k) v j) S /\
    @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(j<k) v j) S /\
    forall k,(M (S-\sum_(j<k) v j)<=
      nonnegative_sequence_tail (fun j=>(a j)%:E) k)%E.
Proof.
move=>hV ha hFinite hMass.
pose p:=fun k=>\sum_(j<k) v j.
pose t:=nonnegative_real_series_tail a.
have hT k:0<=t k:=@nonnegative_real_series_tail_nonnegative R a hFinite k.
have hIncrement k:(M (p k.+1-p k)<=(t k-t k.+1)%:E)%E.
  rewrite /p /t big_ord_recr addrAC subrr add0r
    (@nonnegative_real_series_tail_step R a ha hFinite k).
  exact:hMass k.
have hSmall epsilon:0<epsilon->exists k,t k<epsilon.
  move=>hEpsilon;have[N hN]:=@nonnegative_real_series_tail_small R a ha hFinite epsilon hEpsilon.
  exists N;exact:hN N (leqnn N).
have hCauchy:=@current_mass_cauchy_from_tails R h2 n m U hU p t hT hIncrement hSmall.
have hPrefix k:Rect (p k):=@rectifiable_current_prefix R h2 n m U hU K v hV k.
have[S [hS [hMassLimit hWeak]]]:=@rectifiable_current_mass_cauchy_sequence_limit
  R h2 n m U hU K p hPrefix hCauchy.
exists S;split;first exact:hS.
split;first exact:hMassLimit.
split;first exact:hWeak.
move=>k.
have hDifferenceWeak:=@current_weak_limit_subtract_right R h2 n m U hU p S (p k) hWeak.
have hBound:=@current_mass_weak_closed_bound R h2 n m U hU
  (fun j=>p j-p k) (S-p k) (t k)%:E k hDifferenceWeak
  (fun j hKJ=>@current_mass_increment_tail_bound R h2 n m U hU p t hT hIncrement k j hKJ).
by rewrite (@nonnegative_real_series_tail_value R a hFinite k).
Qed.
End RectifiableCurrentMassSeries.
