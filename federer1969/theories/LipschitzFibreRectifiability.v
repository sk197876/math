(** Federer (1969), 3.2.15, p. 252:
    fibres of a Lipschitz map from R^m to R^n,
    m>n, are countably (H^(m-n),m-n) rectifiable
    for Lebesgue almost every target. Follow the
    full-rank coordinate parametrization and the
    complementary null-fibre reduction of the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoordinateInverseCoverUP CoordinateFibreRectifiability
  FullRankComplementFibreNull RectifiableSetUP LipschitzUP HausdorffMeasure MappingMultiplicity
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_15]: the complete theorem
    in Federer 3.2.15, p. 252. Only m>n and
    global Lipschitzness are assumed. Countable measure
    rectifiability does not assert finite fibre mass;
    target dimension zero remains included. *)
Theorem federer_3_2_15 (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  (n<m)%N -> is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y | @is_countably_measure_m_rectifiable R
      (inner_metric_space (@euclidean_inner_productP R m))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-n))
      (m-n) (mapping_fibre f setT y)].
Proof.
move=> hnm hf.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose mu := @euclidean_lebesgue_measure R n.
pose hm := euclidean_lebesgue_is_measure R n.
pose P := surjective_differential_locus f.
pose phi := @hausdorff_measure R X (m-n).
have hnull := full_rank_complement_fibres_almost_null hnm hf.
apply: (@measure_almost_everywhere_mono R _ mu hm _ _ _ hnull)=> y hy.
split; first exact: hausdorff_measure_is_measure.
exists (mapping_fibre f P y); split.
- exact: full_rank_fibre_countably_rectifiable hf y.
- have he : mapping_fibre f setT y `\` mapping_fibre f P y=
      mapping_fibre f (~` P) y.
    apply/seteqP; split=> x.
    + move=> [[_ hfx] hn]; split=> // hxP; apply: hn; by split.
    + move=> [hn hfx]; split; first by split.
      by move=> [hxP _]; exact: hn hxP.
  by rewrite /measure_almost_included he.
Qed.
