(** Federer (1969), 3.4.8(12), pp. 327, 335:
    the actual components of each analytic stratum inherit
    its local analytic coordinates. The existing convex
    coordinate image is connected and stays in the component
    through its centre. No new chart construction is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerConvex HilbertFormCompactness NormAnalyticUP NormAnalyticLocal NormRegularity
  NormClassZeroTopology NormConvexConnected NormCoordinateSystemUP
  AnalyticSubmanifoldUP AnalyticSubmanifoldCoordinateSystems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_component_coordinates]:
    analytic continuation along the chosen components in
    3.4.8(12), p. 335, uses their original
    convex analytic charts from 3.1.24, p. 240. *)
Theorem analytic_submanifold_component_coordinates (R:realType) n m
    (S:set (R_n R n)) a b:
  @is_euclidean_analytic_submanifold R n m S ->
  @connected_component (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) S a b ->
  exists T V (phi:R_n R n->R_n R m) (psi:R_n R m->R_n R n),
    T b /\is_inner_convex V /\
    @norm_analytic R (R_n R n) (R_n R m)
      (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) T phi /\
    @norm_analytic R (R_n R m) (R_n R n)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) V psi /\
    is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (@connected_component (Topological.clone (real_norm_metric_space
        (inner_norm_real_norm (@euclidean_inner_productP R n))) _) S a)
      T V phi psi 1%N.
Proof.
move=>hS hb.
pose X:=R_n R n;pose Y:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose E:=Topological.clone (real_norm_metric_space hNX) _.
pose F:=Topological.clone (real_norm_metric_space hNY) _.
pose C:=@connected_component E S a.
have hbS:S b:=@connected_component_sub E S a b hb.
have [T [V [phi [psi [hbT [hConvex [hPhi [hPsi hc]]]]]]]]:=
  analytic_submanifold_coordinate_system_exists hS hbS.
have hContinuous:{within (V:set F),continuous (psi:F->E)}.
  apply:continuous_in_subspaceT=>y /asboolP hy.
  exact:(@norm_class_zero_continuous_at R Y X NY NX hNY hNX V psi y
    (norm_class_continuous (norm_analytic_class_all_orders hPsi 0%N)) hy).
have hConnected:@connected E (psi @` V):=
  connected_continuous_connected (@norm_inner_convex_connected R Y NY hNY V hConvex) hContinuous.
have hImageS:(psi @` V) `<=` S.
  move=>x hx;rewrite (norm_coordinate_image hc) in hx;exact:hx.1.
have hbImage:(psi @` V) b by rewrite (norm_coordinate_image hc);split.
have hImageC:(psi @` V) `<=` C.
  rewrite /C (@same_connected_component E S a b hb).
  exact:(@connected_component_max E S (psi @` V) b hbImage hImageS hConnected).
have hImage:psi @` V = C `&` T.
  apply/seteqP;split.
  - move=>x hx;split;first exact:hImageC x hx.
    rewrite (norm_coordinate_image hc) in hx;exact:hx.2.
  - move=>x [hx hxT];rewrite (norm_coordinate_image hc);split;last exact:hxT.
    exact:(@connected_component_sub E S a x hx).
exists T,V,phi,psi;split;first exact:hbT.
split;first exact:hConvex.
split;first exact:hPhi.
split;first exact:hPsi.
constructor.
- exact:norm_coordinate_class_forward hc.
- exact:norm_coordinate_class_backward hc.
- exact:norm_coordinate_forward_range hc.
- exact:hImage.
- exact:norm_coordinate_cancel hc.
Qed.
