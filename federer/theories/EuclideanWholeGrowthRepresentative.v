(** Federer (1969), 3.4.8(13), p. 336:
    the full-dimensional analytic germ admits a compact
    neighbourhood representative with the original uniform diameter
    bound. A closed unit ball retains dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup
  EuclideanClosedBallGrowth MetricClosedBalls MetricBallWholeGerm SetGermUP
  CompactSetDistanceProfile RectifiableSetUP HausdorffMeasure UniformHausdorffGrowthUP
  HausdorffDiameterCost ElementaryHausdorffGrowthRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_whole_growth_representative]: the whole
    germ case of 3.4.8(13), p. 336,
    using a compact neighbourhood of the original origin. *)
Theorem euclidean_whole_growth_representative (R:realType) n:
  exists (S:set (R_n R n)) (c:R),
    @compact (inner_metric_space (@euclidean_inner_productP R n)) S /\
    @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=
      @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 setT /\
    @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n) n S /\
    @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) n S c.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Top:=Topological.clone (real_norm_metric_space hNX) _.
pose S:=@metric_closed_ball R X 0 1.
have hCompact:compact S.
  rewrite /S euclidean_metric_closed_ballE.
  exact:euclidean_closed_ball_compact.
have hNonempty:S !=set0.
  exists (0:X);change (is_true (@mdist R X 0 0<=1));by rewrite mdistxx ler01.
pose K:compact_metric_set X:=exist _ S (mem_set (conj hCompact hNonempty)).
have [hRect hGrowth]:=@compact_ambient_hausdorff_growth R n K.
exists S,(@hausdorff_normalisation R n);split;first exact:hCompact.
split.
- have hEqual:S=@metric_closed_ball R (real_norm_metric_space hNX) 0 1.
    reflexivity.
  rewrite hEqual;exact:(@metric_closed_ball_whole_germ R (real_norm_metric_space hNX) 0 1 ltr01).
by split.
Qed.
