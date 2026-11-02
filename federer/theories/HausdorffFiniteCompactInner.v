(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteCompactMassUP FiniteCompactSuslinInner RealPowerSuslinPositiveCompact RealPowerCompactLimit RealPowerCompactCost CompactSetDistanceProfile CompactGeneratorCostUP CaratheodoryBorelRegular MetricRealPowerMeasureUP MetricRealPowerMeasureLaws BorelRegularMeasureUP MeasureUP TopologicalBorel EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact LipschitzFunctionCompact SuslinSetUP ExtendedRealBoundsUP ExtendedRealBounds RealPowerNaturalHausdorff HausdorffDiameterCost HausdorffMeasureUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_48_real_power_supremum]: corollary
    2.10.48, p. 206, for every nonnegative real degree and
    explicit positive normalising coefficient. The Gamma formula
    for that coefficient remains the separate 2.10.2 obligation. *)
Theorem federer_2_10_48_real_power_supremum (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) S :
  is_metric_real_power_measure c p mu -> (0<c)%R -> (0<=p)%R ->
  is_suslin_set R S -> is_extended_real_supremum (finite_compact_mass_values mu S) (mu S).
Proof.
move=> hmu hc hp hS.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hX : metric_boundedly_compact X by move=> x r _; exact: euclidean_closed_metric_ball_compact.
have hm := metric_real_power_measure_law (ltW hc) hmu.
have hlim := real_power_compact_limit_laws hX (ltW hc) hmu.
have hcost := @real_power_compact_cost_nonnegative_degree R X c p hc hp.
have hnon (C : compact_metric_set X) : 0<=(real_power_compact_generator_cost c p C)%:E.
  rewrite lee_fin; exact (@compact_cost_nonnegative_law R X _ hcost C).
have hr := caratheodory_limit_borel_regular hlim hnon
  (fun C=>closed_borel_set (compact_closed (@metric_hausdorff R X) (set_valP C).1)).
refine (@finite_compact_suslin_supremum R X mu S hm _ _ hS).
- move=> C hC; exact (@borel_regular_borel_measurable R X mu hm hr C (closed_borel_set (compact_closed (@metric_hausdorff R X) hC))).
- move=> T hT hpos; exact: euclidean_real_power_suslin_positive_compact hmu hc hp hT hpos.
Qed.

(** Source for [federer_2_10_48_real_power]: the displayed equality
    in 2.10.48, p. 206, for arbitrary positive coefficients
    and nonnegative real degrees; both infinite and zero values
    of the Suslin set's measure are included. *)
Theorem federer_2_10_48_real_power (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) S :
  is_metric_real_power_measure c p mu -> (0<c)%R -> (0<=p)%R ->
  is_suslin_set R S -> mu S=extended_real_sup (finite_compact_mass_values mu S).
Proof.
move=> hmu hc hp hS.
have hs := federer_2_10_48_real_power_supremum hmu hc hp hS.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (extended_real_supremum_least hs)=> b hb; exact: extended_real_sup_upper hb.
- apply: extended_real_sup_least=> b hb; exact: (extended_real_supremum_upper hs hb).
Qed.

(** Source for [federer_2_10_48_abstract]: corollary 2.10.48,
    p. 206, through the abstract Hausdorff laws with exactly
    the printed natural-degree normalisation. *)
Theorem federer_2_10_48_abstract (R : realType) n m
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) S :
  is_hausdorff_measure m mu -> is_suslin_set R S ->
  mu S=extended_real_sup (finite_compact_mass_values mu S).
Proof.
move=> hmu hS.
exact (@federer_2_10_48_real_power R n (hausdorff_normalisation R m) m%:R mu S
  (@hausdorff_natural_real_power_laws R (inner_metric_space (@euclidean_inner_productP R n)) m mu hmu)
  (hausdorff_normalisation_positive R m) (ltac:(by rewrite ler0n)) hS).
Qed.

(** Source for [federer_2_10_48]: corollary 2.10.48, p. 206,
    for the opaque public Hausdorff measure. The empty set,
    degree zero and ambient dimension zero are allowed. *)
Theorem federer_2_10_48 (R : realType) n m
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S ->
  hausdorff_measure m S=extended_real_sup (finite_compact_mass_values (hausdorff_measure m) S).
Proof. exact: federer_2_10_48_abstract (hausdorff_measure_specification _ m). Qed.
