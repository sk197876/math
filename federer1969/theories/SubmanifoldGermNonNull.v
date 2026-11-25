(** Federer (1969), 3.4.8(13), p. 335:
    a nonempty m-dimensional manifold germ has positive
    H^m measure in every containing representative. Use
    the existing positive-mass coordinate theorem of 3.2.33,
    p. 270, on an actual nonempty local piece. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  SetGermUP SetGermExistence SetGermOrder AnalyticSubmanifoldUP
  AnalyticSubmanifoldCoordinateSystems CoordinateRelativeOpenMass HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_germ_nonnull]: the
    strict positive H^m lower bound for every
    representative in the proof of 3.4.8(13), p. 335.
    Neither the origin's membership in the manifold nor
    measurability of the containing set is required. *)
Theorem analytic_submanifold_germ_nonnull (R:realType) n m
    (Z S:set (R_n R n)):
  @is_euclidean_analytic_submanifold R n m Z ->
  @set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 Z <>
    @set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0 ->
  @set_germ_subset (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0
    (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 Z)
    (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m S<>0%E.
Proof.
move=>hZ hNonempty hSub hNull.
pose E:=Topological.clone (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))) _.
have [O [hO [hO0 hOS]]]:=(@set_germ_subset_original E 0 Z S).1 hSub.
have [b [hbZ hbO]]:exists b,Z b /\O b.
  apply:contrapT=>hEmpty;exfalso;apply:hNonempty;apply/set_germ_equality_original.
  exists O;split;first exact:hO.
  split;first exact:hO0.
  apply/seteqP;split;last by move=>x [hFalse hx];case:hFalse.
  move=>x [hx hxO];exfalso;apply:hEmpty;by exists x.
have [T [V [phi [psi [hbT [hConvex [hPhi [hPsi hc]]]]]]]]:=
  analytic_submanifold_coordinate_system_exists hZ hbZ.
have hNonnull:=coordinate_relative_open_nonnull hc
  ((inner_norm_openP (@euclidean_inner_productP R n) O).2 hO) hbZ hbT hbO.
apply:hNonnull.
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) _ hNull).
by move=>x [[hx hxT] hxO];exact:hOS x hx hxO.
Qed.
