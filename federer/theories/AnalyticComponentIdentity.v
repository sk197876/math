(** Federer (1969), 3.4.8(12), pp. 327, 335:
    an analytic equation which vanishes on a nonempty
    relatively open part of a stratum component vanishes
    on that whole component. Apply the already proved
    zero-locus alternative of 3.2.33, p. 270. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters InnerNormConnectedAdapter
  NormAnalyticUP NormAnalyticOperations NormCoordinateSystemUP AnalyticSubmanifoldUP
  AnalyticSubmanifoldComponentCharts AnalyticChartZeroLocusUP AnalyticChartZeroGlobalAlternative
  CoordinateRelativeOpenMass HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_component_identity]: the last sentence
    in the proof of 3.4.8(12), p. 335.
    The analytic function retains its original domain.
    The component and the open zero piece are actual sets. *)
Theorem analytic_component_identity (R:realType) n m
    (U S O:set (R_n R n)) (f:R_n R n->R^o) a b:
  @is_euclidean_analytic_submanifold R n m S ->S `<=` U ->
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) U f ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) O ->
  @connected_component (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) S a b ->O b ->
  (forall x,S x ->O x ->f x=0) ->
  forall x,@connected_component (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) S a x ->f x=0.
Proof.
move=>hS hSU hf hO hb hbO hZero.
pose X:=R_n R n;pose Y:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose E:=Topological.clone (real_norm_metric_space hNX) _.
pose C:=@connected_component E S a.
pose P:set X:=fun x=>C x /\f x=0.
have hCS:C `<=` S:=@connected_component_sub E S a.
have hCoordinates y (hy:C y):=analytic_submanifold_component_coordinates hS hy.
have hP:@is_analytic_chart_zero_locus R n m C P.
  constructor;first by move=>x hx;exact:hx.1.
  move=>y hy.
  have [T [V [phi [psi [hyT [hConvex [hPhi [hPsi hc]]]]]]]]:=hCoordinates y hy.
  exists T,V,phi,psi,(fun u=>f (psi u));split;first exact:hyT.
  split;first exact:hConvex.
  split;first exact:hc.
  split.
  - exact:(@norm_analytic_compose_on R Y X R^o NY NX (fun t:R^o=>`|t|)
      hNY hNX (@scalar_absolute_value_norm R) V U psi f
      (fun u hu=>hSU _ (hCS _ (norm_coordinate_backward_membership hc hu).1)) hPsi hf).
  - move=>x hx hxT;rewrite (norm_coordinate_base_inverse hc hx hxT).
    by split;[move=>h;exact:h.2|move=>h;split].
have hConnected:@connected (inner_metric_space (@euclidean_inner_productP R n)) C.
  exact:(inner_norm_connectedP (@euclidean_inner_productP R n) C).2 (@component_connected E S a).
case:(analytic_chart_zero_locus_global_alternative hP hConnected)=>[hAll|hNull].
- move=>x hx;have hxP:P x by rewrite hAll;exact:hx.
  exact:hxP.2.
- exfalso.
  have [T [V [phi [psi [hbT [hConvex [hPhi [hPsi hc]]]]]]]]:=hCoordinates b hb.
  have hNonnull:=coordinate_relative_open_nonnull hc
    ((inner_norm_openP (@euclidean_inner_productP R n) O).2 hO) hb hbT hbO.
  apply:hNonnull.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) _ hNull).
  move=>x [[hx hxT] hxO];split;first exact:hx.
  exact:hZero x (hCS x hx) hxO.
Qed.
