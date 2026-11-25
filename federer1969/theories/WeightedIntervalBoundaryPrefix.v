(** Federer (1969), 4.1.12, p. 369:
    each finite original weighted boundary
    sum acts by its signed endpoint
    values, with the original coefficient k.
    Reuse the actual segment boundary and
    the linearity of both original operators. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentPointEvaluation CurrentBoundary ScalarSegmentBoundaryValue
  WeightedIntervalEndpoints WeightedIntervalCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalBoundaryPrefix.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation B := (@current_boundary R h2 1%N 0%N Full hFull).
Local Notation action := (@current_value R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).

(** Source for [weighted_interval_boundary_term_value]:
    the boundary of the original
    k[u_k,v_k] has action k times
    the endpoint difference, supporting Federer
    4.1.12, p. 369. *)
Lemma weighted_interval_boundary_term_value j psi:
  action (B (@weighted_interval_current_term R h2 j)) psi=
    (j.+1)%:R*(zero_form_value (value psi
      (euclidean_one_embed (weighted_interval_right_endpoint R j)))-
      zero_form_value (value psi
        (euclidean_one_embed (weighted_interval_left_endpoint R j)))).
Proof.
by rewrite /weighted_interval_current_term (linZ (hom_linear B))
  (linZ (hom_linear (@current_value R h2 1%N Full hFull 0%N)))
  hom_scaleE scalar_segment_boundary_value.
Qed.

(** Source for [weighted_interval_boundary_prefix_value]:
    every original finite boundary sum
    has its literal signed weighted
    endpoint action, supporting Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_boundary_prefix_value N psi:
  action (B (@weighted_interval_current_prefix R h2 N)) psi=
    \sum_(j<N) (j.+1)%:R*(zero_form_value (value psi
      (euclidean_one_embed (weighted_interval_right_endpoint R j)))-
      zero_form_value (value psi
        (euclidean_one_embed (weighted_interval_left_endpoint R j)))).
Proof.
rewrite /weighted_interval_current_prefix (linear_sum B) current_value_finite_sum.
apply:eq_bigr=>j _;exact:weighted_interval_boundary_term_value.
Qed.
End WeightedIntervalBoundaryPrefix.
