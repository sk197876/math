(** Federer (1969), 3.2.46, p. 282: images of
    the original completed-measurable source subsets are
    measurable and countably measurable for actual target
    Hausdorff measure, as used in 3.2.5, p. 245.
    Target ambient Hausdorff measure is not assumed sigma finite. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianBorelAreaSelection
  RiemannianVolumeFiniteCover RiemannianLipschitzHausdorffImages
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  BorelRegularMeasureUP TopologicalBorel CountablyMeasurableUP
  CountablyMeasurableSubsets ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_lipschitz_measurable_image]:
    the actual original image of every completed-measurable
    source subset is Hausdorff measurable, supporting
    3.2.46, p. 282, through the Borel selection
    argument in 3.2.5(3), p. 245. Neither finite
    source mass nor Borel source measurability is added. *)
Theorem riemannian_lipschitz_measurable_image (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  measure_measurable (riemannian_hausdorff_measure hh m%:R hp) (f @` S).
Proof.
move=> hLip hS.
pose Y := [the topologicalType of riemannian_metric_space hh].
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have [W [hW [hWSub [hWInj [hImageBorel hDeficit]]]]] :=
  @riemannian_borel_area_selection R m n A B g h hg hh f hp S hLip hS.
have hImageMeas := @borel_regular_borel_measurable R Y beta hBeta
  (@riemannian_hausdorff_borel_regular R n B h hh m%:R hp) (f @` W) hImageBorel.
have hDecomposition : f @` S=(f @` W) `|` ((f @` S) `\` (f @` W)).
  apply/seteqP; split=> y.
  - move=> hy; case: (pselect ((f @` W) y))=> hIn; first by left.
    right; by split.
  - move=> [[x hx hxy]|[hy _]]; last exact hy.
    exists x; first exact: (hWSub x hx).1; exact hxy.
rewrite hDecomposition.
exact (@measure_measurable_union R Y beta hBeta _ _ hImageMeas
  (measure_null_measurable hBeta hDeficit)).
Qed.

(** Source for [riemannian_lipschitz_countably_measurable_image]:
    the represented image has a genuine countable finite
    Hausdorff-measure cover, supporting 3.2.46, p. 282,
    and the weight-representation argument of 3.2.5,
    p. 245. This imposes no sigma-finiteness on the
    whole target, and allows infinite original source mass. *)
Theorem riemannian_lipschitz_countably_measurable_image (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  measure_countably_measurable (riemannian_hausdorff_measure hh m%:R hp) (f @` S).
Proof.
move=> hLip hS.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have [C [hCount [hCover hFinite]]] := @measurable_subset_countably_measurable R X mu hMu S setT
  hS (fun x _=>Logic.I) (@riemannian_volume_countably_measurable R m A g hg hp).
have [L [hL hImageBound]] := @riemannian_natural_hausdorff_image_finite_bound R m n A B g h hg hh f hLip.
pose D := (fun T : set X=>f @` T) @` C.
exists D; split; first exact: sub_countable (card_image_le _ _) hCount.
split.
- apply/seteqP; split=> y.
  + move=> [x hx hxy]; rewrite hCover in hx; have [T hT hxT] := hx.
    exists (f @` T); first by exists T.
    by exists x.
  + move=> [E [T hT <-] [x hx hxy]]; exists x; last exact hxy.
    rewrite hCover; by exists T.
- move=> E [T hT <-]; split.
  + exact: (@riemannian_lipschitz_measurable_image R m n A B g h hg hh f hp T hLip (hFinite T hT).1).
  + apply: le_lt_trans (hImageBound m hp T) _.
    have hFiniteReal : mu T \is a fin_num.
      rewrite (ge0_fin_numE (measure_nonnegative hMu T)); exact: (hFinite T hT).2.
    change (is_true (((L^+m)%:E*mu T< +oo)%E)).
    by rewrite -(fineK hFiniteReal) -EFinM ltry.
Qed.
