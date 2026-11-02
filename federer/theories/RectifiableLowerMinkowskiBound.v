(** Federer (1969), 3.2.39, p. 276: lower content
    dominates Hausdorff mass on every genuinely rectifiable source. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP RectifiableFiniteHausdorffMass
  RectifiableGeometricMeasureEquality HausdorffMeasure ProjectionMeasure MinkowskiContents GrossLowerMinkowskiBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_hausdorff_lower_minkowski_bound]:
    the 3.2.37 and 3.2.26 comparison in Federer 3.2.39,
    p. 276. Genuine m-rectifiability proves finite mass and
    the measure-rectifiability hypothesis of 3.2.26. The earlier
    arbitrary-source Gross bound then applies. This supporting
    direction requires neither closedness nor measurability and
    includes the finite multipoint degree-zero convention. *)
Lemma rectifiable_hausdorff_lower_minkowski_bound (R:realType) m n
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->is_m_rectifiable m W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=lower_minkowski_content m W.
Proof.
move=>hmn hW.
have [_ [_ [hGross _]]]:=@federer_3_2_26 R m n hmn W
  (rectifiable_hausdorff_measure_rectifiable hW).
rewrite -hGross; exact:gross_measure_lower_minkowski_bound hmn.
Qed.
