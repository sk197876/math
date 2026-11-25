(** Federer (1969), 3.2.33, p. 270: the source
    unit cube satisfies the standing finite measurable
    (H^m,m)-rectifiability hypotheses of 3.2.32. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  EuclideanOpenUnitCube EuclideanUnitCubeBorel EuclideanLebesgueBoxes EuclideanHausdorffLebesgue
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  RectifiableSetUP EuclideanLipschitzRectifiableImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_unit_cube_measure_rectifiable]:
    the specified W satisfies the conditions of 3.2.32,
    as required in Federer 3.2.33, p. 270.
    The identity parametrization gives countable rectifiability;
    H^m(W)=L^m(W)= 1 proves finite mass. Borel regularity
    proves measurability independently. The supporting result
    also retains the positive-mass zero-dimensional cube. *)
Lemma euclidean_open_unit_cube_measure_rectifiable (R:realType) m:
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m in
  is_measure_m_rectifiable H m (@euclidean_open_unit_cube R m) /\
  measure_measurable H (@euclidean_open_unit_cube R m) /\H (@euclidean_open_unit_cube R m)= 1%E.
Proof.
move=>H.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R m)) m.
have hIdentity:@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_open_unit_cube R m) (fun x=>x).
  exists 1; split; first exact:ltr01.
  split; first exact:ler01; by move=>x y _ _; rewrite mul1r.
have hCount:=euclidean_lipschitz_image_countably_rectifiable hIdentity.
have hImage:(fun x:R_n R m=>x) @` (@euclidean_open_unit_cube R m)=@euclidean_open_unit_cube R m.
  apply/seteqP; split=>x; first by move=>[y hy <-].
  by move=>hx; exists x.
rewrite hImage in hCount.
have hMass:H (@euclidean_open_unit_cube R m)= 1%E.
  rewrite /H (euclidean_hausdorff_spherical_lebesgue (@euclidean_open_unit_cube R m)).1.
  exact:euclidean_unit_cube.
split.
- split; last by rewrite hMass ltry.
  split; first exact hH.
  exists (@euclidean_open_unit_cube R m); split; first exact hCount.
  by rewrite /measure_almost_included setDv /H (measure_empty hH).
split; last exact hMass.
exact:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R
  (inner_metric_space (@euclidean_inner_productP R m)) m) (@euclidean_open_unit_cube_borel R m)).
Qed.
