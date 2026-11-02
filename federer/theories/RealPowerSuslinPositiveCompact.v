(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import SuslinSetUP RealPowerCompactLimit RealPowerCompactCost CompactSetDistanceProfile CompactGeneratorCostUP CompactCostSuslinInner HausdorffFinitePositiveSubset EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact LipschitzFunctionCompact MetricRealPowerMeasureUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_real_power_suslin_positive_compact]:
    2.10.48, p. 206, invokes 2.10.23 and 2.10.47:
    a positive Suslin set contains a finite positive compact subset.
    No finiteness of the original set's measure is assumed. *)
Theorem euclidean_real_power_suslin_positive_compact (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) T :
  is_metric_real_power_measure c p mu -> (0<c)%R -> (0<=p)%R ->
  is_suslin_set R T -> 0<mu T ->
  exists B, [/\ compact B, B `<=` T, 0<mu B & mu B< +oo].
Proof.
move=> hmu hc hp hT hpos.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hX : metric_boundedly_compact X by move=> x r _; exact: euclidean_closed_metric_ball_compact.
have hcost := @real_power_compact_cost_nonnegative_degree R X c p hc hp.
have hlim := real_power_compact_limit_laws hX (ltW hc) hmu.
have hsup := @federer_2_10_23_supremum R X _ hcost mu T hX hlim hT.
have hex : exists C, compact C /\ C `<=` T /\ 0<mu C.
  apply: contrapT=> hnone.
  have hzero : mu T<=0.
    apply: (extended_real_supremum_least hsup)=> b [C [hC [hCT ->]]].
    rewrite leNgt; apply/negP=> hlt; apply: hnone; by exists C.
  by move: hpos; rewrite ltNge hzero.
have [C [hC [hCT hCp]]] := hex.
have [B [hB hBC hBp hBf]] := federer_2_10_47_real_power hmu hc hp hC hCp.
exists B; split=> // x hx; exact: hCT (hBC x hx).
Qed.
