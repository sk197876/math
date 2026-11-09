(** Federer (1969), 3.3.19, p. 304:
    the original Hausdorff and convex first measures
    agree on A after their printed normalization.
    Proved global normalized domination and equal
    finite original masses give the exact restriction
    identity on every test set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP
  CircularDiscExactMass HausdorffMeasure HausdorffClosedCoverAgreement
  IntegralGeometricMeasure IntegralGeometricInfinity IntegralGeometricExponentMonotone CaratheodoryProjectionLength ProjectionBeta
  MeasureUP MeasureBasic MeasureRestriction MeasureScaleIntegral MeasureScaleBorelRegular
  BorelRegularMeasureUP BorelRegularRestriction FiniteBorelMeasureAgreement TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Restrictions.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation B:=(@projection_beta R 2 1 (leqnSn 1) 1).
Local Notation Q:=(@convex_integral_geometric_measure R 2 1 (leqnSn 1) 1).
Local Notation H1:=(@hausdorff_measure R [the metricType R of E] 1).

(** Source for [planar_first_convex_normalized_domination]:
    the normalized exponent comparison used in
    3.3.19, p. 304, also bounds
    every actual original test set: beta_1 Q_1
    is at most H1, by the actual infinity
    endpoint C1=H1. No finiteness is needed. *)
Lemma planar_first_convex_normalized_domination (T:set E):(B%:E*Q T<=H1 T)%E.
Proof.
have h:=@convex_integral_geometric_normalized_measure_monotone R 2 1 (leqnSn 1) 1 +oo T
  (lexx _) (leey _).
by rewrite projection_beta_infinity mul1e convex_integral_geometric_infinity
  (@caratheodory_projection_one_hausdorff_measure R 2 T (erefl true)) in h.
Qed.

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_restricted_normalized_measure_agreement]:
    the restriction identity (H1 restricted to A)/2
    =(Q_1 restricted to A)/pi in 3.3.19,
    p. 304, in its equivalent beta_1 Q_1=H1
    form. The already proved beta_1 pi=2 is
    retained. Use global normalized domination and
    equal finite actual masses to prove equality
    on Borel sets and then every test subset;
    this replaces the printed basis-uniqueness step. *)
Theorem circular_disc_restricted_normalized_measure_agreement (T:set E):
  (B%:E*Q (A `&` T)=H1 (A `&` T))%E.
Proof.
have hQ:=@convex_integral_geometric_measure_is_measure R 2 1 (leqnSn 1) 1 (lexx _).
have hH1:=@hausdorff_measure_is_measure R [the metricType R of E] 1.
have hPositive:0<B:=@projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hScale:=@measure_scale_is_measure R E Q B hQ hPositive.
have hScaleRegular:=@measure_scale_borel_regular R [the topologicalType of E] Q hQ B hPositive
  (@convex_integral_geometric_measure_borel_regular R 2 1 (leqnSn 1) 1 (lexx _)).
have [hNonempty hCompact]:=@circular_disc_limit_nonempty_compact R H hH A hA.
have hBorel:borel_set A:=closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of E]) hCompact).
pose mu:=measure_restrict (measure_scale B Q) A.
pose nu:=measure_restrict H1 A.
have hMu:is_measure mu:=measure_restrict_is_measure hScale A.
have hNu:is_measure nu:=measure_restrict_is_measure hH1 A.
have hMuRegular:=@borel_regular_restrict_borel R [the topologicalType of E]
  (measure_scale B Q) hScale hScaleRegular A hBorel.
have hNuRegular:=@borel_regular_restrict_borel R [the topologicalType of E]
  H1 hH1 (@hausdorff_measure_borel_regular R [the metricType R of E] 1) A hBorel.
have hDominated S:(mu S<=nu S)%E:=planar_first_convex_normalized_domination (A `&` S).
have hTotal:mu setT=nu setT.
  rewrite /mu /nu /measure_restrict /measure_scale !setIT
    (@circular_disc_hausdorff_mass R H hH A hA)
    (@circular_disc_normalized_convex_mass R H hH A hA 1 (lexx _));exact:erefl.
have hFinite:(nu setT< +oo)%E.
  by rewrite /nu /measure_restrict setIT (@circular_disc_hausdorff_mass R H hH A hA) ltry.
have hEqual:=@finite_dominated_borel_regular_measures_agree R [the topologicalType of E]
  mu nu hMu hNu hMuRegular hNuRegular hDominated hTotal hFinite.
exact:(congr1 (fun m:set E-> \bar R=>m T) hEqual).
Qed.
End Restrictions.
