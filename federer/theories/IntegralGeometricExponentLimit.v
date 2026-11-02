(** Federer (1969), 2.10.9, p. 175, displayed left limit: I_t is the limit
    of I_s as s approaches t from below, for 1<t<=infinity. First remove the
    monotonicity restriction on an approaching exponent sequence using
    infima of its tails and normalized-measure monotonicity. Then remove the
    continuously varying positive beta factors. Every target, including a
    non-Borel set or a set of infinite measure, is allowed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  IntegralGeometricExponentMonotone IntegralGeometricNormalizedLimit ProjectionBeta
  ProjectionBetaSequenceLimit RealIncreasingLowerApproximation PositiveNormalizationLimit
  MeasureUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_normalized_exponent_left_limit]:
    supporting normalized version of the limit in Federer
    2.10.9, p. 175, for arbitrary approaching real exponent
    sequences in [1,t]. They may oscillate; their monotonicity
    is not assumed. The target and limit may be infinite. *)
Theorem integral_geometric_normalized_exponent_left_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : nat -> R) (t : \bar R) :
  (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  forall A : set (inner_metric_space (@euclidean_inner_productP R n)),
  extended_order_limit (fun k => (@projection_beta R n m hmn (p k)%:E)%:E *
    @integral_geometric_measure R n m hmn (p k)%:E A)
    ((@projection_beta R n m hmn t)%:E * @integral_geometric_measure R n m hmn t A).
Proof.
move=> hp hl A.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
have [r [hr [hrmon hrlim]]] := @real_increasing_lower_approximation R p t (fun k => (hp k).1) hl.
have hrdom k : (1<=r k)%R /\ (r k)%:E<=t.
  split; first exact: (hr k).1.
  exact: le_trans ((hr k).2 : (r k)%:E<=(p k)%:E) (hp k).2.
have hrl := (@integral_geometric_normalized_left_sequence_limit R n m hmn r t hrdom hrmon hrlim A).2.
split.
- move=> a ha; have [N hN] := hrl.1 a ha; exists N=> k hk.
  apply: lt_le_trans (hN k hk) _.
  exact: (@integral_geometric_normalized_measure_monotone R n m hmn (r k)%:E (p k)%:E A
    (hr k).1 (hr k).2).
- move=> b hb; exists 0%N=> k _; apply: le_lt_trans _ hb.
  exact: (@integral_geometric_normalized_measure_monotone R n m hmn (p k)%:E t A
    (hp k).1 (hp k).2).
Qed.

(** Source for [integral_geometric_exponent_left_limit]: direct
    sequential left-limit formula in Federer 2.10.9, p. 175.
    Every real sequence in [1,t] converging to t has the printed
    measure limit, including t=infinity. No Borel, boundedness,
    finite-measure or sequence-monotonicity hypothesis is added.
    The harmless endpoint t=1 is also allowed. *)
Theorem integral_geometric_exponent_left_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : nat -> R) (t : \bar R) :
  (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  forall A : set (inner_metric_space (@euclidean_inner_productP R n)),
  extended_order_limit (fun k => @integral_geometric_measure R n m hmn (p k)%:E A)
    (@integral_geometric_measure R n m hmn t A).
Proof.
move=> hp hl A.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
apply: (@positive_normalization_sequence_limit R (fun k => @projection_beta R n m hmn (p k)%:E)
  (@projection_beta R n m hmn t) (fun k => @integral_geometric_measure R n m hmn (p k)%:E A)
  (@integral_geometric_measure R n m hmn t A)).
- move=> k; exact: (@projection_beta_positive R n m hmn (p k)%:E (hp k).1).
- exact: (@projection_beta_positive R n m hmn t ht).
- move=> k; exact: (@measure_nonnegative R _ (@integral_geometric_measure R n m hmn (p k)%:E)
    (@integral_geometric_measure_is_measure R n m hmn (p k)%:E (hp k).1) A).
- exact: (@measure_nonnegative R _ (@integral_geometric_measure R n m hmn t)
    (@integral_geometric_measure_is_measure R n m hmn t ht) A).
- exact: (@projection_beta_left_sequence_limit R n m hmn p t hp hl).
- exact: (@integral_geometric_normalized_exponent_left_limit R n m hmn p t hp hl A).
Qed.

(** Source for [federer_2_10_9]: direct printed displayed
    implication in Federer 2.10.9, p. 175, retaining 1<t.
    Limits are expressed by all approaching real exponent
    sequences, with the project's extended-real order topology. *)
Theorem federer_2_10_9 (R : realType) (n m : nat) (hmn : (m<=n)%N) (t : \bar R) :
  1<t -> forall (A : set (inner_metric_space (@euclidean_inner_productP R n))) (p : nat -> R),
  (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  extended_order_limit (fun k => @integral_geometric_measure R n m hmn (p k)%:E A)
    (@integral_geometric_measure R n m hmn t A).
Proof. move=> _ A p hp hl; exact: (@integral_geometric_exponent_left_limit R n m hmn p t hp hl A). Qed.
