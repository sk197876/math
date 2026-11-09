(** Federer (1969), 3.4.5, pp. 318–321: actual
    analytic Taylor coefficient fields, supporting the finite
    coefficient proof of the cited local/global example. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormAnalyticUP NormAnalyticArithmetic NormAnalyticDomain NormAnalyticDerivativeEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficient.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).

(** Source for [is_analytic_directional_coefficient]: the
    actual divided kth differential in a fixed original
    direction, supporting 3.4.5, pp. 318–321. This
    specifies every actual derivative representative without
    choosing a coefficient field or assuming its regularity. *)
Definition is_analytic_directional_coefficient (A:set X) (f:X->Y) k (v:X) (c:X->Y):=
  forall x,A x ->forall z:Z k,
    has_norm_higher_differential NX ev NZ A f k x z ->
    c x=((k`!)%:R)^-1*:@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY [ffun _:'I_k=>v] z.

(** Source for [analytic_directional_coefficient_exists]:
    actual analytic divided Taylor coefficient fields exist,
    supporting 3.4.5, pp. 318–321. Their equations
    and analyticity are proved together from actual derivatives. *)
Theorem analytic_directional_coefficient_exists (A:set X) (f:X->Y) k (v:X):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  exists c:X->Y,is_analytic_directional_coefficient A f k v c /\
    @norm_analytic R X Y NX NY hNX hNY A c.
Proof.
move=>hf.
have [g [hActual hAnalytic]]:=@norm_analytic_derivative_evaluation_exists R X Y NX NY hNX hNY
  A f k [ffun _:'I_k=>v] hf.
exists (fun x=>((k`!)%:R)^-1*:g x);split.
- move=>x hx z hz;by rewrite (hActual x hx z hz).
- move=>x hx;exact:(@norm_analytic_at_scale R X Y NX NY hNX hNY A g x
    ((k`!)%:R)^-1 (hAnalytic x hx)).
Qed.
End Coefficient.
