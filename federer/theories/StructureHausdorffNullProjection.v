(** Federer (1969), 3.3.13, p. 297: condition (I) for
    original Hausdorff-null subsets and every original projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure HausdorffLipschitzImages
  StructureProjectionConditions StructureProjectionContraction MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_hausdorff_null_projection]: supporting
    original condition (I) in Federer 3.3.13, p. 297. Actual Lipschitz
    image comparison from 2.10.11 gives target H^m at most source H^m;
    actual 2.10.35 identifies target H^m with L^m. EVERY original
    subset is allowed; no source measurability or finite-mass premise. *)
Lemma structure_hausdorff_null_projection (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  structure_projection_preserves_null_subsets
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) E p.
Proof.
move=>B _ hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
have hBound:=@hausdorff_lipschitz_image_bound R [the metricType R of X]
  [the metricType R of Y] (euclidean_projection_linear p) 1%R m
  (@structure_projection_lipschitz_one R n m p) B.
rewrite expr1n mul1e hNull (euclidean_hausdorff_spherical_lebesgue _).1 in hBound.
apply/eqP; rewrite eq_le (measure_nonnegative (euclidean_lebesgue_is_measure R m)) andbT.
exact:hBound.
Qed.
