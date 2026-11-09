(** Federer (1969), 3.4.2(7), p. 313: the finite derivative
    expansion transfers the flatness limits to ζ. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP PartialFunctionUP RelativeDifferential
  PositiveRightOrderLimit RadialRatioZero FinitePositiveRadiusCutoff
  CriticalOscillation CriticalFiniteDerivativeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_finite_derivative_oscillation_limit]: the
    limit of the finite sum in 3.4.2(7), p. 313. A common positive
    cutoff makes every function oscillation small; the derivative
    expansion then gives a small bound for ζ. This includes an
    empty basis and infinite oscillations away from the cutoff. *)
Theorem critical_finite_derivative_oscillation_limit (R:realType) m
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (T G:set (R_n R m)) (f:R_n R m->Y)
    (I:finType) (e:I->R_n R m) (fi:I->R_n R m->Y) lambda:
  (forall i c,G c ->fi i c=0) ->
  (forall z,Z z ->inner_norm (@euclidean_inner_productP R m) z<=1 ->
    exists a:I->R,(forall i,`|a i|<=1) /\z=\sum_i a i*:e i) ->
  (forall x,T x ->forall (L:partial_function (R_n R m) Y) z y (a:I->R),
    partial_function_graph (relative_norm_differential
      (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY T T f) x L ->
    partial_function_graph L z y ->z=\sum_i a i*:e i ->y=\sum_i a i*:fi i x) ->
  (forall i,positive_right_extended_order_limit
    (fun delta=>critical_eta NY Z T G (fi i) lambda delta) 0%E) ->
  positive_right_extended_order_limit
    (fun delta=>critical_zeta hNY Z T G f lambda delta) 0%E.
Proof.
move=>hZero hCoordinates hFormula hLimits.
apply:nonnegative_positive_right_limit_zero.
- move=>delta hdelta;exact:critical_zeta_nonnegative.
- move=>epsilon hEpsilon.
  pose N:=(#|I|)%:R:R.
  have hN:0<=N by rewrite /N ler0n.
  have hDen:0<N+1 by lra.
  pose a:=epsilon/(N+1).
  have ha:0<a by rewrite /a divr_gt0.
  have hEach i:exists d:R,0<d /\forall delta:R,0<delta<d ->
      (critical_eta NY Z T G (fi i) lambda delta<a%:E)%E.
    have haE:(0<a%:E)%E by rewrite lte_fin.
    have [d [hd hSmall]]:=(hLimits i).2 a%:E haE.
    exists d;split;first exact:hd.
    move=>delta /andP[hPositive hCutoff];exact:hSmall delta hPositive hCutoff.
  have [d [hd hCommon]]:=@finite_common_positive_radius_bound R I
    (fun i delta=>(critical_eta NY Z T G (fi i) lambda delta<a%:E)%E) hEach.
  exists d;split;first exact:hd.
  move=>delta hPositive hCutoff.
  have hSmall:0<delta<d by apply/andP;split.
  have hBound:=@critical_finite_derivative_oscillation_bound R m Y NY hNY Z T G f I e fi
    (fun _=>a) lambda delta (fun _=>ltW ha) hZero hCoordinates hFormula
    (fun i=>ltW (hCommon delta hSmall i)).
  have hValue:(\sum_(i:I) a)=N*a.
    by rewrite sumr_const cardT /N mulr_natl -cardE.
  have hCancel:(N+1)*a=epsilon by rewrite /a mulrC divfK // gt_eqF.
  have hStrict:N*a<epsilon by nra.
  apply:(le_lt_trans hBound).
  by rewrite hValue lte_fin.
Qed.
