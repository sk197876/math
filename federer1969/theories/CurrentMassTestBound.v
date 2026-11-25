(** Federer (1969), 4.1.7, p. 358, used in
    4.1.12, p. 368: each original compact test
    has a positive uniform comass bound, and its
    finite-mass action obeys the original homogeneous estimate.
    Reuse the compact zeroth seminorm and 4.1.5's gauge bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothFunctionTopology
  SmoothFunctionSeminormFamily SmoothDerivativeSeminormUP CurrentCompactZerothBounds CurrentMassSealed CurrentMassBasic
  DistributionVariationDomain DistributionVariationFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMassTestBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation UT := [the choiceType of set_type (U:set (real_norm_metric_space hNX))].

(** Source for [current_test_positive_comass_bound]: every
    original test has a positive finite uniform comass
    bound on U, by its compact support and the
    zeroth seminorm of Federer 4.1.1, p. 344.
    This supports the mass-closure comparison in 4.1.12,
    p. 368, including an empty open domain. *)
Theorem current_test_positive_comass_bound (phi:DT):
  exists a:R,0<a /\forall x,U x->NY (value phi x)<=a.
Proof.
have[K hK]:=smooth_test_support_bound hE phi.
pose b:=smooth_function_derivative_seminorm hD K 0%N (smooth_test_inclusion hE phi).
have hb:0<=b:=smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hD K 0%N) _.
exists (b+1);split;first by lra.
move=>x hx.
case:(pselect (SmoothCompactSet.smooth_compact_carrier K x))=>hKx.
- have hBound:=@current_compact_zeroth_point_bound R h2 n m U hU K
    (smooth_test_inclusion hE phi) x hKx.
  change (is_true (NY (value phi x)<=b)) in hBound;lra.
- have hZero: value phi x=0:=
    (@smooth_function_compact_support_iff R X Y NX NY hNX hNY U E ev hE K
      (smooth_test_inclusion hE phi)).1 hK x hKx.
  rewrite hZero (real_seminorm_zero hNY.1);lra.
Qed.

(** Source for [current_finite_mass_test_bound]: an actual
    test with pointwise comass at most a>0 satisfies
    |T(phi)|<=a M(T), by the original gauge estimate
    of Federer 4.1.5, p. 349, and current
    mass of 4.1.7, p. 358. No support
    or representation premise is imposed on T. *)
Theorem current_finite_mass_test_bound (T:C) (phi:DT) a b:
  @CurrentMass.value R h2 n m U hU T=b%:E->0<a->
  (forall x,U x->NY (value phi x)<=a)->
  `|@current_value R h2 n U hU m T phi|<=a*b.
Proof.
move=>hMass ha hPhi.
pose dvalues:=@distribution_domain_values R (real_norm_metric_space hNX) U Y DT
  (smooth_test_values_hom hE).
have hGauge:=@current_mass_majorant_one R h2 n m U hU T.
rewrite hMass in hGauge.
apply:(@distribution_variation_finite_scaled_bound R UT Y NY hNY DT dvalues
  (@current_value R h2 n U hU m T) (fun _=>1) b a hGauge ha phi)=>x.
rewrite mulr1;exact:hPhi (set_val x) (set_valP x).
Qed.
End CurrentMassTestBound.
