(** Federer (1969), 3.4.8(16), p. 337:
    a relatively open set meeting the regular manifold
    germ has positive measure in that manifold's dimension.
    Reuse the actual coordinate mass theorem of 3.2.33. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters EuclideanSubmanifoldUP
  SetGermUP SetGermExistence SetGermOrder AnalyticSubmanifoldUP
  AnalyticSubmanifoldCoordinateSystems CoordinateRelativeOpenMass HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_relative_open_manifold_mass]: the original
    point z and neighbourhood V in the proof of
    3.4.8(16), p. 337. Relative openness supplies
    V; the existing chart theorem supplies positive H^m
    measure on its actual nonempty manifold piece. *)
Theorem analytic_relative_open_manifold_mass (R:realType) n m
    (S T Z:set (R_n R n)):
  let E:=Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _ in
  @is_euclidean_analytic_submanifold R n m Z ->
  @relatively_open_set E S T ->
  set_germ_subset (@set_germ E 0 Z) (@set_germ E 0 S) ->
  @set_germ E 0 (T `&` Z)<>@set_germ E 0 set0 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m T<>0%E.
Proof.
move=>E hZ [W [hW hT]] hSub hNonempty hNull.
have [O [hO [hO0 hOS]]]:=(@set_germ_subset_original E 0 Z S).1 hSub.
have [b [[hbT hbZ] hbO]]:exists b,(T `&` Z) b /\O b.
  apply:contrapT=>hEmpty;exfalso;apply:hNonempty;apply/set_germ_equality_original.
  exists O;split;first exact:hO.
  split;first exact:hO0.
  apply/seteqP;split;last by move=>x [hFalse hx];case:hFalse.
  move=>x [hx hxO];exfalso;apply:hEmpty;by exists x.
have hbW:W b by move:hbT;rewrite hT=>[[_ hbW]].
have [V [C [phi [psi [hbV [hConvex [hPhi [hPsi hc]]]]]]]]:=
  analytic_submanifold_coordinate_system_exists hZ hbZ.
have hOpen:@open (inner_metric_space (@euclidean_inner_productP R n)) (O `&` W).
  apply/(inner_norm_openP (@euclidean_inner_productP R n) (O `&` W)).
  exact:openI hO hW.
have hNonnull:=coordinate_relative_open_nonnull hc hOpen hbZ hbV (conj hbO hbW).
apply:hNonnull.
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) _ hNull).
move=>x [[hxZ hxV] [hxO hxW]];rewrite hT;split;last exact:hxW.
exact:hOS x hxZ hxO.
Qed.
