(** Federer (1969), 3.1.24, pp. 238–240:
    continuous polynomials satisfy the analytic Taylor condition.
    This supplies the affine and quadratic scalar maps used
    in the inverse-majorant calculation on p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormRegularity
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor PolynomialTaylorExactExpansion
  PolynomialHigherDifferentials ContinuousSymmetricFormAdapter NormClassInfinityPolynomial
  NormAnalyticUP NormAnalyticPolynomialSeries NormPolynomialSeriesAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_polynomial_function_analytic_at]: supporting
    the analytic scalar quadratic expression in Federer 3.1.24,
    p. 240. A polynomial with continuous coefficient forms
    has an exact finite Taylor expansion by 3.1.11, p. 221,
    so the uniform Taylor condition holds at every centre.
    Target completeness and the proved four-condition equivalence
    give analyticity. Constants and the zero polynomial are included. *)
Theorem norm_polynomial_function_analytic_at (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (P:PolynomialFunction X Y) a :
  (forall i,(i<(polynomial_degree P).+1)%N ->
    norm_bounded_symmetric_form NX NY (sform_component i (polynomial_to_forms P))) ->
  @norm_analytic_at R X Y NX NY hNX hNY setT P a.
Proof.
move=>hP.
pose Z:=fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev:=fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN:=fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ:=fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have hopen x (_:True):norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact ltr01; by move=>v hv.
have hclass:=@norm_class_infinity_polynomial_function R X Y NX NY hNX hNY Z ev ZN hZ
  (fun _=>True) hopen P hP.
have [D [he hD]]:=@polynomial_higher_differential_fields_exist R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) hopen P hP.
have htaylor:@norm_taylor_analytic_at R X Y NX NY hNX hNY setT P a.
  exists setT; split; first exact Logic.I.
  split; first by move=>x hx.
  split; first exact hclass.
  exists (fun i=>D i a); split; first by move=>i; exact (hD i a Logic.I).
  move=>eps heps; exists (polynomial_degree P)=>N hN x hx.
  have hsum:P x= \sum_(i<N.+1) (i`!)%:R^-1*:@ev i [ffun j=>x-a] (D i a).
    have hh:=@polynomial_taylor_formula_any_higher_order R (@pchar_num R) X Y P N a (x-a) hN.
    have hshift:a+(x-a)= x by rewrite addrC subrK.
    rewrite hshift in hh; rewrite hh.
    apply: eq_bigr=>i _; rewrite he sform_polynomial_diagonal_value.
    congr (_*:polynomial_taylor_coefficient P i a _).
    apply: eq_from_tnth=>j; by rewrite !tnth_mktuple ?ffunE.
  by rewrite -hsum subrr (real_seminorm_zero hNY.1).
exact (@norm_polynomial_series_analytic R X Y NX NY hNX hNY hcomplete setT P a
  (@norm_taylor_analytic_polynomial R X Y NX NY hNX hNY setT P a htaylor)).
Qed.

(** Source for [norm_polynomial_function_analytic]: continuous
    polynomials are analytic functions, supporting the affine
    and quadratic terms in Federer 3.1.24, p. 240. *)
Theorem norm_polynomial_function_analytic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (P:PolynomialFunction X Y) :
  (forall i,(i<(polynomial_degree P).+1)%N ->
    norm_bounded_symmetric_form NX NY (sform_component i (polynomial_to_forms P))) ->
  @norm_analytic R X Y NX NY hNX hNY setT P.
Proof.
move=>hP a _; exact (@norm_polynomial_function_analytic_at R X Y NX NY hNX hNY hcomplete P a hP).
Qed.
