(** Supporting Fubini and continuous reparametrisation in Federer (1969),
    2.10.16, p. 178: the actual product of Lebesgue measure and theta-star
    is Borel regular. This follows from their existing regularity and the
    countable bases already proved for the two parameter spaces. it does not
    state this integral-geometric instance. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueHaar EuclideanProjectionMetric OrthogonalProjectionProbability
  ProjectionJointMultiplicity BorelRegularMeasureUP ProductBorelRegularity
  SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [projection_product_measure_borel_regular]:
    supporting closed-set measurability for the parameter
    products used in 2.10.16, p. 178. Both countable
    bases and both factor regularities are discharged. *)
Lemma projection_product_measure_borel_regular (R : realType) (n m : nat)
    (hmn : (m<=n)%N) : is_borel_regular_measure (@projection_product_measure R n m hmn).
Proof.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
have [U hU] := euclidean_countable_open_base R m.
have [D [hc hd]] := orthogonal_projection_metric_separable R n m.
pose V := @SeparableMetricBase.value R P D hc hd.
have hV := @SeparableMetricBase.laws R P D hc hd.
exact (@product_measure_borel_regular R Y P (@euclidean_lebesgue_measure R m)
  (@orthogonal_projection_probability R n m hmn) (@euclidean_lebesgue_is_measure R m)
  (@theta_star_is_measure R n m hmn) U V hU hV
  (@euclidean_lebesgue_borel_regular R m) (@theta_star_borel_regular R n m hmn)).
Qed.
