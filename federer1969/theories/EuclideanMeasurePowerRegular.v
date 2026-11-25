(** Federer (1969), 2.10.29, p. 195: Borel regularity and local
    power-density estimates for the finite Euclidean products of the
    competing measure. Derive both from the sealed first-factor and
    successor laws, using existing Euclidean homeomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanMeasurePowerUP EuclideanMeasurePower EuclideanBlockCoordinates EuclideanMetricProduct EuclideanLebesgueHaar
  MeasureUP ProductMeasure BorelRegularMeasureUP ProductBorelRegularity MeasureCoordinateTransport
  MetricCartesianRectangleBounds PowerCoverDensityUP PowerCoverDensityProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Regularity.
Variable R : realType.
Variable d : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variable nu : set (E d) -> \bar R.
Variable hn : is_measure nu.

(** Source for [euclidean_measure_power_borel_regular]: supporting
    Borel regularity of the actual finite
    Euclidean product measures used in 2.10.29,
    p. 195. No finiteness or sigma-finiteness
    premise on nu is needed. *)
Theorem euclidean_measure_power_borel_regular :
  is_borel_regular_measure nu -> forall q,
    is_borel_regular_measure (@euclidean_measure_power R d nu hn q).
Proof.
move=> hr; elim=> [|q ih]; first by rewrite euclidean_measure_power_firstE.
rewrite euclidean_measure_power_successorE /paired_product_measure.
pose a := euclidean_power_dimension d q.
have he : (fun p : E a*E d=>@euclidean_block_join R a d (p.1,p.2))=(@euclidean_block_join R a d).
  apply: funext=> p; by case: p.
rewrite he.
have [U hU] := @euclidean_countable_open_base R a.
have [V hV] := @euclidean_countable_open_base R d.
have hprod := @product_measure_borel_regular R (E a) (E d) _ _
  (@euclidean_measure_power_is_measure R d nu hn q) hn U V hU hV ih hr.
exact (@homeomorphic_pushforward_borel_regular R (Topological.clone (E a*E d)%type _) (E (a+d))
  _ (product_measure_is_measure (@euclidean_measure_power_is_measure R d nu hn q) hn)
  (@euclidean_block_join R a d) (@euclidean_block_split R a d)
  (@euclidean_block_joinK R a d) (@euclidean_block_splitK R a d)
  (@euclidean_block_join_continuous R a d) (@euclidean_block_split_continuous R a d) hprod).
Qed.

(** Source for [euclidean_measure_power_vanishing_density]: supporting
    multiplication of the local exponent by
    the number of factors in 2.10.29,
    p. 195. The density property is
    proved, not assumed by the measure-power
    specification; exponent zero remains included. *)
Theorem euclidean_measure_power_vanishing_density (p : R) :
  0<=p -> is_borel_regular_measure nu -> is_vanishing_power_cover_density p nu ->
  forall q, is_vanishing_power_cover_density (q.+1%:R * p)%R (@euclidean_measure_power R d nu hn q).
Proof.
move=> hp hr hd; elim=> [|q ih].
- by rewrite euclidean_measure_power_firstE mul1r.
- have hcast : (q.+2%:R * p=q.+1%:R * p+p)%R.
    by rewrite -[q.+2]addn1 natrD mulrDl mul1r.
  rewrite hcast euclidean_measure_power_successorE.
  exact (@paired_product_vanishing_power_density R [the metricType R of E (euclidean_power_dimension d q+d)]
    [the metricType R of E (euclidean_power_dimension d q)] [the metricType R of E d]
    (fun x y=>@euclidean_block_join R (euclidean_power_dimension d q) d (x,y))
    (fun x=>(@euclidean_block_split R (euclidean_power_dimension d q) d x).1)
    (fun x=>(@euclidean_block_split R (euclidean_power_dimension d q) d x).2)
    (@euclidean_blocks_are_metric_product R (euclidean_power_dimension d q) d) _ _
    (@euclidean_measure_power_is_measure R d nu hn q) hn (q.+1%:R * p)%R p
    (mulr_ge0 (@ler0n R q.+1) hp) hp (euclidean_measure_power_borel_regular hr q) hr ih hd).
Qed.
End Regularity.
