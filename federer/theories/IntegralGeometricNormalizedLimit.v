(** Federer (1969), 2.10.9, p. 175: normalized precursor of the printed
    left-exponent measure limit. Apply the Borel-partition theorem to beta_t
    zeta_t, whose increasing probability-norm limit is proved even on
    unbounded sets. The positive rescaling identity identifies its
    independently constructed measure with beta_t I_t. Countable common
    Borel hulls retain arbitrary targets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  IntegralGeometricExponentMonotone IntegralGeometricGaugeLeftContinuity ProjectionBeta
  BorelCoverCostUP BorelCaratheodoryMeasure BorelCaratheodoryScale BorelCaratheodoryIncreasingCosts
  BorelClosedProjection TopologicalBorel ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_normalized_left_sequence_limit]:
    supporting normalized form of the displayed limit in
    Federer 2.10.9, p. 175. Every nondecreasing real exponent
    sequence in [1,t] approaching t gives increasing convergence
    of beta_p I_p to beta_t I_t on all targets, including
    non-Borel targets and infinite values. *)
Theorem integral_geometric_normalized_left_sequence_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : nat -> R) (t : \bar R) :
  (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  (forall k l, (k<=l)%N -> (p k<=p l)%R) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  forall A : set (inner_metric_space (@euclidean_inner_productP R n)),
  extended_increases_to (fun k => (@projection_beta R n m hmn (p k)%:E)%:E *
    @integral_geometric_measure R n m hmn (p k)%:E A)
    ((@projection_beta R n m hmn t)%:E * @integral_geometric_measure R n m hmn t A).
Proof.
move=> hp hmon hl A.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose c (s : \bar R) (B : set X) := (@projection_beta R n m hmn s)%:E *
  @integral_geometric_gauge R n m hmn s B.
have hc s : 1<=s -> is_borel_cover_cost (c s).
  move=> hs; exact: (@borel_cover_cost_scale R X (@integral_geometric_gauge R n m hmn s)
    (@integral_geometric_gauge_borel_cover_cost R n m hmn s hs)
    (@projection_beta R n m hmn s) (ltW (@projection_beta_positive R n m hmn s hs))).
have hcost B : borel_set B -> extended_increases_to (fun k => c (p k)%:E B) (c t B).
  move=> hB; have hS := @metric_borel_suslin R X B hB; split.
  - move=> k l hkl; exact: (@integral_geometric_normalized_gauge_monotone R n m hmn B
      (p k)%:E (p l)%:E hS (hp k).1 (hmon k l hkl)).
  - exact: (@integral_geometric_normalized_gauge_left_sequence_limit R n m hmn B p t hS hp hl).
have [D [hD hden]] := euclidean_metric_separable R n.
have hh := @borel_caratheodory_increasing_cost_limit R X (c t) (fun k => c (p k)%:E) D
  (hc t ht) (fun k => hc (p k)%:E (hp k).1) hD hden hcost A.
have he s : 1<=s -> borel_caratheodory_measure (c s) A=
    (@projection_beta R n m hmn s)%:E * @integral_geometric_measure R n m hmn s A.
  move=> hs; exact: (@borel_caratheodory_positive_scale R X
    (@integral_geometric_gauge R n m hmn s)
    (@integral_geometric_gauge_borel_cover_cost R n m hmn s hs)
    (@projection_beta R n m hmn s) (@projection_beta_positive R n m hmn s hs) A).
have hseq : (fun k => borel_caratheodory_measure (c (p k)%:E) A)=
    (fun k => (@projection_beta R n m hmn (p k)%:E)%:E *
      @integral_geometric_measure R n m hmn (p k)%:E A).
  apply: funext=> k; exact: he (p k)%:E (hp k).1.
by rewrite hseq (he t ht) in hh.
Qed.
