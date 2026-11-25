(** Federer (1969), 4.1.12, p. 369:
    the actual original product T times T
    takes the harmonic partial-sum values on
    the literal psi_M. Use the original
    separated-test characterisation and the proved
    endpoint action T(phi_k)=k. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentCartesianDomain CurrentSpaces
  CurrentPointEvaluation CurrentCartesianProductUP CurrentCartesianProductSealed CurrentCartesianTestProductSealed
  ReciprocalPowerSeriesBounds ReciprocalPowerSeriesWeights WeightedIntervalCurrentLaws
  WeightedIntervalCutoffSealed WeightedIntervalBoundaryCutoffAction WeightedIntervalProductTests HarmonicPrefixBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalProductAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation AB := (@euclidean_cartesian_set R 1%N 1%N Full Full).
Local Notation hAB := (@current_cartesian_domain_open R 1%N 1%N Full Full hFull hFull).
Local Notation T := (@weighted_interval_boundary R h2).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation TT := (@CartesianCurrentProduct.value R h2 1%N 1%N 0%N 0%N Full Full hFull hFull T T).
Local Notation action := (@current_value R h2 (1+1)%N AB hAB 0%N).
Local Notation term := (@weighted_interval_product_test_term R h2).
Local Notation psi := (@weighted_interval_product_test R h2).

(** Source for [weighted_interval_product_term_action]:
    the original kth weighted product
    test has action k^(-1) on
    the actual T times T,
    supporting Federer 4.1.12, p. 369. *)
Lemma weighted_interval_product_term_action n:
  action TT (term n)=((n.+1)%:R:R)^-1.
Proof.
rewrite /weighted_interval_product_test_term.
rewrite (linZ (hom_linear (@current_value R h2 (1+1)%N AB hAB 0%N TT))).
rewrite ((@CartesianCurrentProduct.laws R h2 1%N 1%N 0%N 0%N Full Full hFull hFull T T).1
  (phi n) (phi n)) !weighted_interval_boundary_cutoff_action.
change (reciprocal_power_series_weight R 3%N n*((n.+1)%:R*(n.+1)%:R)=((n.+1)%:R:R)^-1).
rewrite -expr2;exact:reciprocal_cube_endpoint_square_product.
Qed.

(** Source for [weighted_interval_product_test_action]:
    the original (T times T)(psi_M)
    is precisely sum_[k<=M] 1/k,
    the displayed divergent actions in
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_product_test_action M:
  action TT (psi M)=harmonic_partial_sum R M.
Proof.
rewrite /weighted_interval_product_test
  (linear_sum (@current_value R h2 (1+1)%N AB hAB 0%N TT)) harmonic_partial_sumE.
apply:eq_bigr=>j _;exact:weighted_interval_product_term_action.
Qed.
End WeightedIntervalProductAction.
