(** Federer (1969), 3.3.7, p. 294: the bounded original
    projected image has finite mass under its local ball estimate. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIndexedCover MetricClosedBalls
  ContainedCompactFiniteNet FiniteSeparatedMetricNetUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_compact_subset_ball_mass_finite]: supporting
    finiteness needed for the actual Radon measure psi in Federer
    3.3.7, p. 294. Original E lies in an actual compact K, and
    a finite net with centres in E gives a finite outer-mass bound.
    Neither original E nor its projected-image counterpart is assumed
    closed or measurable. The empty target is retained. *)
Theorem structure_compact_subset_ball_mass_finite (R:realType) (X:metricType R)
    (x0:X) (E K:set X) (psi:set X-> \bar R) (b delta:R):
  compact K ->E `<=` K ->is_measure psi ->0<delta ->0<=b ->
  (forall x,E x ->(psi (metric_closed_ball x delta)<=b%:E)%E) ->
  (psi E< +oo)%E.
Proof.
move=>hCompact hEK hPsi hDelta hb hBall.
have [F hNet]:=@contained_compact_finite_separated_metric_net_exists R X x0 E K delta
  hCompact hEK hDelta.
have hCount:countable [set` F]:=finite_set_countable (finite_fset F).
have hCover:=finite_metric_net_covers hNet.
have hBound:=@measure_indexed_cover R X X psi hPsi E [set` F]
  (fun x=>metric_closed_ball x delta) hCount hCover.
have hTerms x:[set` F] x ->(psi (metric_closed_ball x delta)<=b%:E)%E.
  move=>hx; apply:hBall.
  exact:(finite_metric_net_inside hNet hx).
have hSum:=nonnegative_sum_mono hTerms.
have hTotal:=le_trans hBound hSum.
have hNonnegative x:x \in F ->(0<=b%:E)%E by move=>_; rewrite lee_fin.
rewrite (nonnegative_sum_finite hNonnegative) sumEFin in hTotal.
exact:le_lt_trans hTotal (ltry _).
Qed.
