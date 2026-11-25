(** Federer (1969), 4.1.12, p. 369: one
    common unit-comass test calibrates every positive
    interval summand, giving the exact original
    total mass. Pass its actions to the
    actual testwise series limit and use
    the proved quantitative mass tails for the upper bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation CurrentCoefficientNorms
  CurrentGlobalComassSealed CurrentGlobalComassBound CurrentMassSealed CurrentMassBasic CurrentWeakSequenceLimit
  NonnegativeSum NonnegativeSequenceTail NonnegativeRealSeriesPrefixConvergence NormSequenceLimitUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_calibrated_series_mass]: if
    one actual original unit-comass test takes
    the nonnegative values a_k on all
    summands, and their actual series has
    the original mass-tail bounds, its mass
    is exactly sum a_k. This supports
    the printed equality in Federer 4.1.12,
    p. 369, without assuming that equality. *)
Theorem current_calibrated_series_mass (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (v:nat->@current_space R h2 n U hU m) (S:@current_space R h2 n U hU m)
    (a:nat->R) (phi:@current_test_space R h2 n U hU m):
  (forall k,0<=a k)->(nonnegative_sum setT (fun k=>(a k)%:E)< +oo)%E->
  (forall x,U x->@current_form_comass R h2 n m (@current_test_value R h2 n U hU m phi x)<=1)->
  (forall k,@current_value R h2 n U hU m (v k) phi=a k)->
  @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(j<k) v j) S->
  (forall k,(@CurrentMass.value R h2 n m U hU (S-\sum_(j<k) v j)<=
    nonnegative_sequence_tail (fun j=>(a j)%:E) k)%E)->
  @CurrentMass.value R h2 n m U hU S=nonnegative_sum setT (fun k=>(a k)%:E).
Proof.
move=>ha hFinite hUnit hAction hWeak hTail.
pose A:=nonnegative_sum setT (fun k=>(a k)%:E).
have hNumber:A \is a fin_num.
  rewrite ge0_fin_numE;last exact:nonnegative_sum_nonnegative.
  exact:hFinite.
have hPrefix k:@current_value R h2 n U hU m (\sum_(j<k) v j) phi=\sum_(j<k) a j.
  rewrite current_value_finite_sum;apply:eq_bigr=>j _;exact:hAction j.
have hValue:@current_value R h2 n U hU m S phi=fine A.
  apply:(@norm_sequence_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
    (fun k=>@current_value R h2 n U hU m (\sum_(j<k) v j) phi) _ _ (hWeak phi)).
  move=>epsilon hEpsilon.
  have[N hN]:=@nonnegative_real_series_prefix_convergence R a ha hFinite epsilon hEpsilon.
  exists N=>k hNk;rewrite hPrefix;exact:hN k hNk.
have hUpper:(@CurrentMass.value R h2 n m U hU S<=A)%E.
  have h:=hTail 0%N;rewrite big_ord0 subr0 in h.
  have hSet:[set k:nat|(0<=k)%N]=setT.
    apply/seteqP;split=>k _;first exact:Logic.I.
    exact:leq0n.
  by rewrite /nonnegative_sequence_tail hSet in h.
have hGlobal:(@CurrentGlobalComass.value R h2 n m U (@current_test_value R h2 n U hU m phi)<=1)%E.
  exact:(@current_global_comass_bound R h2 n m U (@current_test_value R h2 n U hU m phi) 1).2 hUnit.
have hLower:=@current_mass_unit_test_upper R h2 n m U hU S phi hGlobal.
rewrite hValue (fineK hNumber) in hLower.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.
