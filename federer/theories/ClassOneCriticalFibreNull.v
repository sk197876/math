(** Federer (1969), 3.2.31, p. 269: supporting vanishing
    of the critical fibres of a class-one map. Exhaust its
    closed low-rank locus by compact ball restrictions, and
    combine the compact estimates outside one null target set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormClassOneUP LinearRankAtLeast MetricClosedBalls EuclideanClosedBallCompact
  ClassOneLowRankClosed ClassOneCriticalCompactFibre CountableNullFibreCover
  HausdorffMeasure HausdorffFibreCutoffs NullFibresProperSource ZeroUpperIntegral
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ClassOneCriticalNull.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [class_one_low_rank_fibres_almost_null]: supporting
    zero critical-fibre contribution in Federer 3.2.31, p. 269.
    Every subset of the actual rank-below-mu locus has zero
    complementary fibre mass for H^mu almost every target point.
    No compactness, measurability, finite mass or global Lipschitz
    bound is assumed on that subset or on the class-one map. *)
Theorem class_one_low_rank_fibres_almost_null (G:X->Y)
    (D:X->Hom (R_n R m) (R_n R v)) (A:set X) k mu:
  (0<v)%N ->(0<mu)%N ->m=(k+mu)%N ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT G D ->
  (forall x,A x ->~linear_rank_at_least (D x) mu) ->
  measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass G A k y=0].
Proof.
move=>hv hmu hDim hG hA.
pose S:set X:=[set x|~linear_rank_at_least (D x) mu].
have hS:closed S:=@class_one_low_rank_locus_closed R m v mu G D hG.
pose C n:=S `&` metric_closed_ball (0%R:X) (n%:R:R).
have hC n:compact (C n).
  rewrite /C setIC; exact (compact_closedI (@euclidean_closed_metric_ball_compact R m (0%R:X) (n%:R:R)) hS).
have hCover:A `<=` \bigcup_n C n.
  move=>x hx.
  have [n _ hBall]:=@metric_natural_closed_balls_cover R X (0%R:X) x Logic.I.
  exists n=>//; by split=>//; exact:hA.
have hNull n:measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass G (C n) k y=0].
  have hZero:=@class_one_critical_compact_fibre_integral_zero R m v G D (C n) k mu
    hv hmu hDim hG (hC n) (fun x hx=>hx.1).
  apply:(nonnegative_zero_upper_integral_almost_zero (@hausdorff_measure_is_measure R Y mu) _ hZero)=>y.
  exact (@measure_nonnegative R X (@hausdorff_measure R X k)
    (@hausdorff_measure_is_measure R X k) (C n `&` G @^-1` [set y])).
exact (@almost_null_fibres_countable_cover R X Y (@hausdorff_measure R X k)
  (@hausdorff_measure R Y mu) (@hausdorff_measure_is_measure R X k)
  (@hausdorff_measure_is_measure R Y mu) G A C hCover hNull).
Qed.
End ClassOneCriticalNull.
