(** Federer (1969), 3.2.23, p. 260, first proof paragraph:
    a rectifiable first factor times a Hausdorff-null second factor
    is null in the sum dimension. The positive-degree parametrization
    is supplied by 3.2.14 and 2.10.43. The finite-set convention
    in degree zero is handled by a finite family of constant maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanSquaredProduct
  HausdorffProductNullFactor HausdorffProductSliceMeasure HausdorffMeasure HausdorffRestrictedLipschitz
  RectifiableSetUP EuclideanRectifiableGlobalParametrization LipschitzUP LipschitzBasic
  MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_parametrized_product_null_factor]: the
    first null-product argument of Federer 3.2.23, p. 260,
    by 2.10.45, pp. 202–203. No boundedness, measurability
    or finite-mass assumption on the first set is needed after
    a single globally Lipschitz parametrization is supplied. *)
Lemma lipschitz_parametrized_product_null_factor (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->W `<=` f @` setT ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z=0%E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (m+mu) (euclidean_cartesian_set W Z)=0%E.
Proof.
move=>[L [hL hf]] hW hZ.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+v)).
pose Y:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose F:=euclidean_cartesian_map f (@id (R_n R v)).
have hF:@is_metric_lipschitz_bound R X Y
    (euclidean_cartesian_set setT Z) F (L+1).
  apply:euclidean_cartesian_map_lipschitz_bound.
  - apply:(metric_lipschitz_bound_increase hf); by rewrite lerDl ler01.
  - have hOne:1<=L+1 by rewrite lerDr; exact:ltW hL.
    split; first exact:(le_trans ler01 hOne).
    move=>x y _ _; rewrite -[leLHS]mul1r.
    apply:ler_wpM2r; first exact:mdist_ge0.
    by rewrite lerDr; exact:ltW hL.
have hZero:@hausdorff_measure R X (m+mu) (euclidean_cartesian_set setT Z)=0%E.
  rewrite (addnC m mu).
  exact:(@hausdorff_product_slice_null_factor R m mu X
    (inner_metric_space (@euclidean_inner_productP R v))
    (fun x z=>euclidean_block_join (x,z))
    (fun p=>(@euclidean_block_split R m v p).1)
    (fun p=>(@euclidean_block_split R m v p).2)
    (euclidean_blocks_are_squared_metric_product R m v) Z hZ setT).
have hBound:=@hausdorff_lipschitz_on_bound R X Y (euclidean_cartesian_set setT Z) F (L+1) (m+mu)%N
  (euclidean_cartesian_set setT Z) hF (@subset_refl X (euclidean_cartesian_set setT Z)).
rewrite hZero mule0 in hBound.
have hImage:euclidean_cartesian_set W Z `<=` F @` euclidean_cartesian_set setT Z.
  move=>p [hpW hpZ].
  have [x _ hfx]:=hW _ hpW.
  exists (euclidean_block_join (x,(euclidean_block_split p).2)).
  - change (True /\ Z (euclidean_block_split
      (euclidean_block_join (x,(euclidean_block_split p).2))).2).
    by rewrite euclidean_block_joinK; split.
  - rewrite /F /euclidean_cartesian_map euclidean_block_joinK /= hfx.
    exact:euclidean_block_splitK.
apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R Y (m+mu))) andbT.
exact:(le_trans (measure_mono (@hausdorff_measure_is_measure R Y (m+mu)) hImage) hBound).
Qed.

(** Source for [rectifiable_product_null_factor]: the full first
    proof paragraph of Federer 3.2.23, p. 260. The m=0
    case uses the printed finite-set convention of 3.2.14,
    p. 252, so it does not incorrectly assume that every
    zero-rectifiable set is the image of one point. *)
Theorem rectifiable_product_null_factor (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z=0%E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (m+mu) (euclidean_cartesian_set W Z)=0%E.
Proof.
case:m=>[|m] hW hZ.
- pose Y:=inner_metric_space (@euclidean_inner_productP R (n+v)).
  pose rho:=@hausdorff_measure R Y (0+mu).
  have hr:=@hausdorff_measure_is_measure R Y (0+mu).
  have hPoint w:rho (euclidean_cartesian_set [set w] Z)=0%E.
    apply:(@lipschitz_parametrized_product_null_factor R 0 n mu v [set w] Z (fun _=>w)).
    + exists 1; split; first exact:ltr01; split; first exact:ler01.
      move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
    + move=>y ->; exists (0%R:R_n R 0); by [].
    + exact hZ.
  have hCover:euclidean_cartesian_set W Z `<=`
      \bigcup_(w in W) euclidean_cartesian_set [set w] Z.
    move=>p [hpW hpZ]; exists (euclidean_block_split p).1; first exact hpW.
    by split.
  exact:(measure_null_subset hr hCover (measure_null_countable_union hr
    (finite_set_countable hW) (fun w _=>hPoint w))).
- have [A [f [_ [hf hImage]]]]:=positive_rectifiable_global_parametrization hW.
  apply:(lipschitz_parametrized_product_null_factor hf _ hZ).
  move=>w hw; rewrite -hImage in hw; have [x _ hfx]:=hw; by exists x.
Qed.
