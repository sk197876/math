(** Federer (1969), 4.1.12, p. 368: the
    boundary of the original interval series is
    supported in the actual dyadic endpoint set.
    Each finite boundary sum has that support;
    original testwise convergence preserves it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  AlternatingForms AlternatingZero CurrentSpaces CurrentPointEvaluation CurrentBoundary CurrentDirac
  OrientedSegmentCurrentBoundary CurrentSupportGeometry SmoothFunctionSupport SmoothTestSpaces
  DyadicEndpointSupportGeometry SmoothCompactSet DyadicCurrentEndpointArithmetic DyadicCurrentEndpointIndices DyadicCurrentEndpointCompact
  DyadicIntervalCurrentUP DyadicIntervalCurrentSealed DyadicIntervalCurrentLaws DyadicIntervalBoundaryPrefix CurrentWeakLimitOperations CurrentFormSupportValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DyadicIntervalBoundarySupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation K := (dyadic_current_endpoint_compact R).
Local Notation S := (@DyadicIntervalCurrent.value R h2).
Local Notation B := (@current_boundary R h2 1%N 0%N Full hFull).
Local Notation support := (@current_support R h2 1%N Full hFull 0%N).
Local Notation prefix := (@dyadic_interval_current_prefix R h2).

(** Source for [dyadic_interval_boundary_prefix_support]:
    every finite original endpoint sum is
    supported in the literal compact endpoint
    set, supporting Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_boundary_prefix_support k:
  support (B (prefix k)) `<=` smooth_compact_carrier K.
Proof.
apply:(@current_support_compact_criterion R h2 1%N 0%N Full hFull K (B (prefix k))).2=>psi hPsi.
rewrite dyadic_interval_boundary_prefix_value.
have hZero (a:R) (hA:dyadic_endpoint_set R a):
    @current_test_value R h2 1%N Full hFull 0%N psi (euclidean_one_embed a)=0.
  have hNo:~@current_test_support R h2 1%N 0%N Full hFull psi (euclidean_one_embed a).
    move=>hIn;apply:(hPsi _ hIn).2.
    change (dyadic_endpoint_set R (euclidean_one_project (euclidean_one_embed a))).
    by rewrite euclidean_one_embedK.
  exact:(@current_form_value_outside_support R h2 1%N 0%N Full hFull
    (smooth_test_inclusion (@current_smooth_space_laws R h2 1%N Full hFull 0%N) psi)
    (euclidean_one_embed a) Logic.I hNo).
apply:big1=>j _.
by rewrite (hZero _ (dyadic_current_right_endpoint_in_set R j))
  (hZero _ (dyadic_current_left_endpoint_in_set R j)) subrr.
Qed.

(** Source for [dyadic_interval_boundary_support]:
    the actual boundary T has support in
    the original compact dyadic endpoint set,
    as asserted in Federer 4.1.12, p. 368.
    No representation hypothesis is imposed on T. *)
Theorem dyadic_interval_boundary_support:
  support (@dyadic_interval_boundary R h2) `<=` smooth_compact_carrier K.
Proof.
apply:(@current_weak_limit_support_compact R h2 1%N 0%N Full hFull K
  (fun k=>B (prefix k)) (B S)).
- exact:(@current_weak_limit_boundary R h2 1%N 0%N Full hFull prefix S
    (@DyadicIntervalCurrent.laws R h2)).
- exact:dyadic_interval_boundary_prefix_support.
Qed.
End DyadicIntervalBoundarySupport.
