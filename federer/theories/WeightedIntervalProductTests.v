(** Federer (1969), 4.1.12, p. 369:
    the literal original psi_M is the
    finite sum of k^(-3) phi_k(x)phi_k(y).
    Use actual compact tests and the
    preceding opaque separated-test map of 4.1.8. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingZero AlternatingDual AlternatingProduct ScalarCoefficients ZeroFormScalarProduct
  CurrentCartesianDomain CurrentSpaces CurrentPushforwardDirac CurrentTestValueLaws CurrentTestPointValues
  CurrentCartesianTestProductSealed ReciprocalPowerSeriesBounds WeightedIntervalCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalProductTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Z := (R_n R (1+1)%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation AB := (@euclidean_cartesian_set R 1%N 1%N Full Full).
Local Notation hAB := (@current_cartesian_domain_open R 1%N 1%N Full Full hFull hFull).
Local Notation DC := (@current_test_space R h2 (1+1)%N AB hAB 0%N).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).

(** Source for [weighted_interval_product_test_term]:
    the actual original kth summand
    k^(-3) phi_k(x)phi_k(y), supporting Federer
    4.1.12, p. 369. *)
Definition weighted_interval_product_test_term n:DC:=
  reciprocal_power_series_weight R 3%N n*:
    @CartesianTestProduct.value R h2 1%N 1%N Full Full hFull hFull 0%N 0%N (phi n) (phi n).

(** Source for [weighted_interval_product_test]: the
    literal first M terms of
    the original psi_M in Federer
    4.1.12, p. 369. *)
Definition weighted_interval_product_test M:DC:=\sum_(j<M) weighted_interval_product_test_term j.

(** Source for [weighted_interval_product_test_term_values]:
    the original weighted separated test
    has precisely coefficient k^(-3)
    phi_k(x)phi_k(y), supporting the displayed
    psi_M formula in Federer 4.1.12,
    p. 369. Use the already
    proved zero-degree pullback and scalar product laws. *)
Theorem weighted_interval_product_test_term_values n z:AB z->
  zero_form_value (@current_test_value R h2 (1+1)%N AB hAB 0%N
    (weighted_interval_product_test_term n) z)=
  reciprocal_power_series_weight R 3%N n*
    (zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi n)
      (@euclidean_first_block_map R 1%N 1%N z))*
    zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi n)
      (@euclidean_last_block_map R 1%N 1%N z))).
Proof.
move=>hz.
rewrite /weighted_interval_product_test_term current_test_scale_value
  (linZ (@zero_form_value_linear R Z R^o))
  ((@CartesianTestProduct.laws R h2 1%N 1%N Full Full hFull hFull 0%N 0%N).2
    (phi n) (phi n) z hz).
rewrite -{1}(zero_form_valueK (A_m_dual
  (hom_as_linear (@euclidean_first_block_map R 1%N 1%N))
  (@current_test_value R h2 1%N Full hFull 0%N (phi n)
    (@euclidean_first_block_map R 1%N 1%N z)))).
by rewrite original_zero_form_wedge_scalar (linZ (@zero_form_value_linear R Z R^o))
  !current_pullback_zero_coefficient.
Qed.

(** Source for [weighted_interval_product_test_values]:
    the actual original psi_M has
    exactly its displayed scalar finite-sum
    formula at every product point,
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_product_test_values M z:AB z->
  zero_form_value (@current_test_value R h2 (1+1)%N AB hAB 0%N
    (weighted_interval_product_test M) z)=
  \sum_(j<M) reciprocal_power_series_weight R 3%N j*
    (zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi j)
      (@euclidean_first_block_map R 1%N 1%N z))*
    zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi j)
      (@euclidean_last_block_map R 1%N 1%N z))).
Proof.
move=>hz;rewrite /weighted_interval_product_test current_test_finite_sum_value
  (linear_sum (@zero_form_value R Z R^o)).
apply:eq_bigr=>j _;exact:weighted_interval_product_test_term_values hz.
Qed.
End WeightedIntervalProductTests.
