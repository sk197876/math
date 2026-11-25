(** Federer (1969), 3.4.8(13), p. 336:
    a null exceptional source does not affect the
    coordinate multiplicity bound almost everywhere. The
    existing Lipschitz null-image theorem applies to every
    original coordinate projection, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ExteriorIndices CoordinateProjection ProjectionNorm EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue MappingMultiplicity CountingMeasure LipschitzUP NullLipschitzArea
  HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_projection_metric_contraction]: the
    actual p_lambda is nonexpanding, 1.7.7, p. 34,
    as used in the projection estimate of
    3.4.8(13), p. 336. *)
Lemma coordinate_projection_metric_contraction (R:realType) n m
    (lambda:Lambda n m) (x y:inner_metric_space (@euclidean_inner_productP R n)):
  @mdist R (inner_metric_space (@euclidean_inner_productP R m))
    (@coordinate_projection R n m lambda x) (@coordinate_projection R n m lambda y)<=
    @mdist R (inner_metric_space (@euclidean_inner_productP R n)) x y.
Proof.
rewrite !inner_metric_distanceE -linearB.
have hProjection:=(O_star_projection _).1 (@coordinate_projection_orthogonal R n m lambda).
exact:(@orthogonal_projection_norm_bound R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _) hProjection (x-y)).
Qed.

(** Source for [coordinate_multiplicity_null_remainder_bound]:
    N(p_lambda|S,y)<=k_lambda for almost every y,
    from the actual model fibre bound and null
    exceptional part, 3.4.8(13), p. 336.
    No measurability of S or Z is assumed. *)
Theorem coordinate_multiplicity_null_remainder_bound (R:realType) n m
    (lambda:Lambda n m) (S Z:set (R_n R n)) (c: \bar R):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (S `\` Z)=0%E ->
  (forall y,(@mapping_multiplicity R [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    (R_n R m) (@coordinate_projection R n m lambda) Z y<=c)%E) ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|(@mapping_multiplicity R [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      (R_n R m) (@coordinate_projection R n m lambda) S y<=c)%E].
Proof.
move=>hNull hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose p:=@coordinate_projection R n m lambda.
pose beta:=@euclidean_lebesgue_measure R m.
have hBeta:=@euclidean_lebesgue_is_measure R m.
have hLip:@is_metric_lipschitz_bound R X Y setT p 1.
  split;first exact:ler01.
  by move=>x y hx hy;rewrite mul1r;exact:coordinate_projection_metric_contraction.
have hImage:=@null_hausdorff_lipschitz_image R X Y p 1 m (S `\` Z) hLip hNull.
have hImageNull:beta (p @` (S `\` Z))=0%E.
  by rewrite (euclidean_hausdorff_spherical_lebesgue (p @` (S `\` Z))).1 in hImage.
have hGood:measure_almost_everywhere beta (~` (p @` (S `\` Z))).
  by rewrite /measure_almost_everywhere setCK.
apply:(measure_almost_everywhere_mono hBeta _ hGood)=>y hy.
apply:(le_trans _ (hBound y)).
apply:(measure_mono (@counting_measure_is_measure R (Choice.clone X _)))=>x [hx hpx].
split;last exact:hpx.
apply:contrapT=>hxNotZ;apply:hy;exists x;last exact:hpx.
by split.
Qed.
