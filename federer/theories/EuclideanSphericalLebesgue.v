(** Federer (1969), 2.10.35, printed p. 197: the density-one fact and
    2.10.19(3) imply S^n(A)<=L^n(V) for every open V containing A. Let the
    positive density threshold increase to one, then use the proved Radon
    outer regularity of Lebesgue measure. This follows Federer's density
    route *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueCompactInner
  EuclideanLebesgueDensity HausdorffMeasure MetricDensities SphericalMetricDensityTheorems
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel RadonMeasureUP ExtendedContractionSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_spherical_measure_lebesgue_bound]: direct
    last two inequalities in the proof
    of 2.10.35, p. 197. Targets
    may be arbitrary, with infinite measure
    allowed. Natural dimension zero is retained. *)
Theorem euclidean_spherical_measure_lebesgue_bound (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A<=euclidean_lebesgue_measure n A)%E.
Proof.
apply: (radon_outer_greatest (@euclidean_lebesgue_radon R n))=> V hV hAV.
apply: (@extended_contraction_squeeze R _ _ (measure_nonnegative (euclidean_lebesgue_is_measure R n) V))=> t /andP[ht0 ht1].
apply: (@federer_2_10_19_3 R (inner_metric_space (@euclidean_inner_productP R n)) n
  (@euclidean_lebesgue_measure R n) A V t (euclidean_lebesgue_is_measure R n) _ hV hAV).
- move=> S hS; apply: (borel_regular_borel_measurable
    (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_borel_regular R n)).
  exact: closed_borel_set hS.
- move=> x hx; rewrite (euclidean_lebesgue_upper_lower_density x).1 lte_fin.
  exact: ht1.
Qed.
