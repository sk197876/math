(** Federer (1969), 3.2.45, p. 279:
    continuity of Q_t(A) on the whole original
    extended exponent interval, for every A. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  ConvexIntegralGeometricFiniteExponentLimit ConvexIntegralGeometricInfinityLimit
  ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedOrderLimitTopology
  ExtendedRealCountableBaseSealed CountableBaseSequentialLimit ExtendedClosedNeighborhoods
  RelativeLimitClosureContinuity FiniteExponentPart ExtendedExponentInterval
  ExtendedIntervalFiniteDensity CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_measure_continuous]:
    the complete continuity assertion of Federer 3.2.45,
    p. 279, for the actual Q_t measures of every
    target set A. Domain and codomain carry the original
    extended-real order topology. The domain includes both
    one and infinity. No measurability, boundedness, positive
    mass or finite mass hypothesis is added to A. The
    finite-exponent proof uses the corrected convex secant;
    infinity uses a separate proved uniform projection modulus. *)
Theorem convex_integral_geometric_measure_continuous (R : realType) n m
    (hMN : (m <= n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  continuous (fun t : subspace [set t : extended_real_line R | 1 <= t] =>
    (@convex_integral_geometric_measure R n m hMN t A : extended_real_line R)).
Proof.
pose D : set (extended_real_line R) := [set t | 1 <= t].
have hInterval : is_extended_real_interval D.
  move=> s t p hS hT hSP hPT; exact: le_trans hS hSP.
have hClosed : closed D.
  exact: (@order_closed_upper_ray_closed _
    [the orderTopologicalType _ of order_topology (\bar R)] (1 : \bar R)).
have hClosureD : closure D = D := esym ((closure_id D).1 hClosed).
have hClosure := @extended_interval_finite_part_closure R D 1%R hInterval
  (fun t hT => hT) (lexx 1).
rewrite hClosureD in hClosure.
have hContinuous : continuous (fun t : subspace (closure (finite_exponent_part D)) =>
    (@convex_integral_geometric_measure R n m hMN t A : extended_real_line R)).
  apply: relative_limits_continuous_on_closure.
  - exact: extended_real_closed_neighborhood_refinement.
  - move=> t hT.
    apply: (@countable_base_sequential_relative_limit (extended_real_line R) (extended_real_line R)
      (@ExtendedRealCountableBase.value R) (@ExtendedRealCountableBase.laws R)).
    move=> u hU hTopLimit; apply/extended_order_limit_topology_iff.
    have hLimit := (extended_order_limit_topology_iff u t).1 hTopLimit.
    pose p j := fine (u j).
    have hValue j : (p j)%:E = u j by rewrite /p fineK //; exact: (hU j).2.
    have hP j : (1 <= p j)%R.
      have h := (hU j).1.
      change (is_true (1 <= u j)) in h.
      by rewrite -(hValue j) lee_fin in h.
    have hSequence : (fun j => (p j)%:E) = u by apply: funext=> j; exact: hValue.
    have hT1 : 1 <= t by rewrite hClosure in hT.
    have hOutput : (fun j => @convex_integral_geometric_measure R n m hMN (u j) A) =
        (fun j => @convex_integral_geometric_measure R n m hMN (p j)%:E A).
      apply: funext=> j; by rewrite hValue.
    rewrite hOutput; rewrite -hSequence in hLimit.
    clear hT hTopLimit.
    case: t hT1 hLimit=> [q| |] hT1 hLimit.
    + exact: (@convex_integral_geometric_finite_exponent_sequence_limit R n m hMN p q A hP hT1 hLimit).
    + exact: (@convex_integral_geometric_infinity_sequence_limit R n m hMN p A hP hLimit).
    + by move: hT1; rewrite leNgt ltNyr.
by rewrite hClosure in hContinuous.
Qed.
