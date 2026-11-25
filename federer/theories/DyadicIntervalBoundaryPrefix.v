(** Federer (1969), 4.1.12, p. 368: the
    boundary of a finite original interval
    sum acts by its signed endpoint values.
    Reuse the actual segment boundary formula
    of 4.1.8, p. 362, and
    the original linear evaluation maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  AlternatingForms AlternatingZero CurrentSpaces CurrentPointEvaluation CurrentBoundary CurrentDirac
  OrientedSegmentCurrentBoundary DyadicCurrentEndpointArithmetic DyadicIntervalCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DyadicIntervalBoundaryPrefix.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation B := (@current_boundary R h2 1%N 0%N Full hFull).
Local Notation action := (@current_value R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).

(** Source for [dyadic_interval_boundary_term_value]:
    the boundary of each original summand
    acts as evaluation at its right endpoint
    minus evaluation at its left endpoint,
    supporting Federer 4.1.12, p. 368. *)
Lemma dyadic_interval_boundary_term_value j psi:
  action (B (@dyadic_interval_current_term R h2 j)) psi=
    zero_form_value (value psi (euclidean_one_embed (dyadic_current_right_endpoint R j)))-
    zero_form_value (value psi (euclidean_one_embed (dyadic_current_left_endpoint R j))).
Proof.
rewrite /dyadic_interval_current_term oriented_segment_current_boundary.
pose E:=@current_point_evaluation R h2 1%N 0%N Full hFull psi.
change (E (@dirac_current R h2 1%N Full hFull
    (euclidean_one_embed (dyadic_current_right_endpoint R j))-
    @dirac_current R h2 1%N Full hFull
    (euclidean_one_embed (dyadic_current_left_endpoint R j)))=
    zero_form_value (value psi (euclidean_one_embed (dyadic_current_right_endpoint R j)))-
    zero_form_value (value psi (euclidean_one_embed (dyadic_current_left_endpoint R j)))).
rewrite (linB (hom_linear E)) /E !current_point_evaluation_values.
by rewrite !dirac_current_evaluation.
Qed.

(** Source for [dyadic_interval_boundary_prefix_value]:
    every original finite boundary sum has
    precisely its signed finite endpoint action,
    supporting Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_boundary_prefix_value k psi:
  action (B (@dyadic_interval_current_prefix R h2 k)) psi=
    \sum_(j<k) (zero_form_value (value psi
      (euclidean_one_embed (dyadic_current_right_endpoint R j)))-
      zero_form_value (value psi (euclidean_one_embed (dyadic_current_left_endpoint R j)))).
Proof.
rewrite /dyadic_interval_current_prefix (linear_sum B) current_value_finite_sum.
apply:eq_bigr=>j _;exact:dyadic_interval_boundary_term_value.
Qed.
End DyadicIntervalBoundaryPrefix.
