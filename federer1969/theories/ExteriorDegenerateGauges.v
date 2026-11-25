(** Supporting boundary cases for Federer (1969), 2.10.3, pp. 171–172. The
    printed positive integer degree need not be at most the ambient
    dimension. Apply the exterior-power dimension theorem of 1.3.2, pp.
    14–15, and equal-endpoint products to check these cases with the actual
    gauge. Source context and algebra context: ExteriorDiameterUP.v. These
    are supporting consequences, not further printed claims. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteCoordinates FiniteExteriorPowers ExteriorNorm ExteriorDiameterUP ExteriorDiameterLaws
  ExteriorDiameter ExteriorMeasureGauge ExteriorMeasureUP ExteriorMeasure HausdorffLengthUP
  MetricDiameter MetricDiameterMaps MetricScaleWeightedBound CaratheodoryLimitUP
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [exterior_difference_norm_above_dimension]:
    supporting m>n boundary of Federer 2.10.3,
    p. 171, from 1.3.2, pp. 14–15. Every
    degree-m exterior vector is zero, so the actual
    induced exterior norm of each endpoint product is zero. *)
Lemma exterior_difference_norm_above_dimension (R : realType) (n m : nat)
    (a b : 'I_m -> R_n R n) : (n<m)%N -> exterior_difference_norm a b=0%R.
Proof.
move=> hnm; rewrite /exterior_difference_norm.
rewrite (@exterior_power_above_dimension R n (R_n R n)
  (@coordinate_basis R n) (@coordinate_basisP R n) (real_exterior_two_nonzero R) m hnm
  (exterior_difference_product a b)).
exact: exterior_norm_zero.
Qed.

(** Source for [exterior_diameter_cost_above_dimension]:
    supporting zero gauge for degrees m>n in Federer
    2.10.3, p. 171. This includes unbounded sets;
    it follows from the exterior dimension theorem,
    rather than a finite metric-diameter assumption. *)
Theorem exterior_diameter_cost_above_dimension (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (n<m)%N -> exterior_diameter_cost m A=0.
Proof.
move=> hnm.
have hz : extended_exterior_diameter m A=0.
  apply/eqP; rewrite eq_le (exterior_diameter_nonnegative (extended_exterior_diameter_specification m A)) andbT.
  apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m A))=> // a b ha hb.
  by rewrite (exterior_difference_norm_above_dimension a b hnm).
by rewrite /exterior_diameter_cost hz mule0.
Qed.

(** Source for [exterior_diameter_cost_singleton]: supporting
    positive-degree zero-size boundary of the endpoint
    formula in Federer 2.10.3, p. 171. All endpoints
    in a singleton coincide, so a factor vanishes. *)
Lemma exterior_diameter_cost_singleton (R : realType) (n m : nat)
    (x : inner_metric_space (@euclidean_inner_productP R n)) :
  (0<m)%N -> exterior_diameter_cost m [set x]=0.
Proof.
move=> hm.
have hz : extended_exterior_diameter m [set x]=0.
  apply/eqP; rewrite eq_le (exterior_diameter_nonnegative (extended_exterior_diameter_specification m [set x])) andbT.
  apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m [set x]))=> // a b ha hb.
  have hab : a=b by apply: funext=> i; exact: eq_trans (ha i) (esym (hb i)).
  by rewrite hab (exterior_difference_equal_endpoints b hm).
by rewrite /exterior_diameter_cost hz mule0.
Qed.

(** Source for [exterior_measure_positive_singleton_zero]:
    supporting singleton mass in Federer 2.10.3,
    pp. 171–172, from its zero-cost singleton cover
    at every positive cutoff. The target degree is
    positive as in the printed definition. *)
Theorem exterior_measure_positive_singleton_zero (R : realType) (n m : nat)
    (x : inner_metric_space (@euclidean_inner_productP R n)) :
  (0<m)%N -> @exterior_diameter_measure R n m [set x]=0.
Proof.
move=> hm; apply/eqP; rewrite eq_le
  (measure_nonnegative (@exterior_diameter_measure_is_measure R n m)) andbT.
apply: (caratheodory_limit_least (@exterior_diameter_measure_specification R n m))=> delta nu hd hn.
pose j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
  @exist _ (fun A : set (inner_metric_space (@euclidean_inner_productP R n)) => A \in [set A | A !=set0])
    [set x] (mem_set (ex_intro _ x (erefl x))).
have hsize : extended_metric_diameter (val j)<=delta.
  change (extended_metric_diameter [set x]<=delta).
  rewrite extended_metric_diameter_singleton; exact: ltW hd.
have hh := @metric_scale_generator_bound R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) delta nu j hn
  (exterior_diameter_cost_nonnegative m (val j)) hsize.
change (is_true (nu [set x]<=exterior_diameter_cost m [set x])) in hh.
by rewrite (exterior_diameter_cost_singleton x hm) in hh.
Qed.

(** Source for [exterior_measure_positive_countable_zero]:
    supporting countable-cover boundary of Federer
    2.10.3, pp. 171–172, using the countable
    subadditivity of 2.1.2, p. 53. This includes
    finite and empty targets without a nonemptiness premise. *)
Theorem exterior_measure_positive_countable_zero (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> countable A -> @exterior_diameter_measure R n m A=0.
Proof.
move=> hm hA; have hmu := @exterior_diameter_measure_is_measure R n m.
have hcov : A `<=` \bigcup_(x in A) [set x] by move=> x hx; exists x.
have hh := measure_indexed_cover hmu hA hcov.
rewrite (nonnegative_sum_zero (fun x _ => @exterior_measure_positive_singleton_zero R n m x hm)) in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative hmu).
Qed.
