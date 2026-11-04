(** Federer (1969), 3.2.48, p. 285: the actual source product
    is a class-one manifold when its original factors are manifolds.
    Supporting proof from the coordinate criterion in 3.1.19(4),
    p. 231, with all Cartesian and Euclidean chart laws discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness ProductInner FiniteInnerChartUP
  FiniteInnerSubmanifoldUP FiniteInnerSubmanifoldCoordinates FiniteInnerCoordinatesSubmanifold
  FiniteInnerCartesianChart FiniteInnerCoordinateParameterChart InnerCartesianCoordinateSystems
  NormCoordinateSystemUP NormRegularity NormDifferentialUP InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_cartesian_submanifold]: the original
    Cartesian manifold used for the Jacobian computation in 3.2.48,
    p. 285. Actual local product coordinates prove this assertion;
    no product-manifold or selected chart is an additional premise. *)
Theorem finite_inner_cartesian_submanifold (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    r s k (M:set V) (N:set W):
  (1<=k)%N ->is_inner_submanifold BV r k M ->is_inner_submanifold BW s k N ->
  is_inner_submanifold (product_inner hV hW) (r+s)%N k [set z:V*W|M z.1 /\N z.2].
Proof.
move=>hk hM hN.
have [n [e [p [hChartV hMV]]]]:=hM.
have [v [f [q [hChartW hNW]]]]:=hN.
pose hP:=product_inner_productP hV hW.
pose E:=finite_inner_cartesian_direct e f.
pose Q:=finite_inner_cartesian_inverse p q.
have hChart:=finite_inner_cartesian_chart hV hW hChartV hChartW.
pose idR:Hom (R_n R r) (R_n R r):=hom_of_linear (linear_id (R_n R r)).
pose idS:Hom (R_n R s) (R_n R s):=hom_of_linear (linear_id (R_n R s)).
have hR:is_finite_inner_chart (@euclidean_inner_product R r) idR idR.
  constructor; [by move=>u|by move=>u|by move=>u v0].
have hS:is_finite_inner_chart (@euclidean_inner_product R s) idS idS.
  constructor; [by move=>u|by move=>u|by move=>u v0].
pose hRS:=product_inner_productP (@euclidean_inner_productP R r) (@euclidean_inner_productP R s).
pose eRS:=finite_inner_cartesian_direct idR idS.
pose pRS:=finite_inner_cartesian_inverse idR idS.
have hParamChart:=finite_inner_cartesian_chart (@euclidean_inner_productP R r)
  (@euclidean_inner_productP R s) hR hS.
apply:(@finite_inner_coordinates_submanifold R [the lmodType R of (V*W)%type]
  _ hP (n+v)%N E Q (r+s)%N k [set z:V*W|M z.1 /\N z.2] hk hChart).
move=>a [haM haN].
have [T [U [phi [psi [hBase [hConv hC]]]]]]:=
  @finite_inner_submanifold_coordinates R V BV hV r k M a.1 hM haM.
have [T' [U' [phi' [psi' [hBase' [hConv' hC']]]]]]:=
  @finite_inner_submanifold_coordinates R W BW hW s k N a.2 hN haN.
have hProduct:=@inner_cartesian_coordinate_system R V W (R_n R r) (R_n R s)
  BV BW _ _ hV hW (@euclidean_inner_productP R r) (@euclidean_inner_productP R s)
  M T N T' U U' phi psi phi' psi' k hC hC'.
have hCoordinates:=@finite_inner_coordinate_parameter_chart R [the lmodType R of (V*W)%type]
  [the lmodType R of (R_n R r*R_n R s)%type] _ _ hP hRS (r+s)%N eRS pRS
  [set z:V*W|M z.1 /\N z.2] [set z:V*W|T z.1 /\T' z.2]
  [set z:R_n R r*R_n R s|U z.1 /\U' z.2]
  (fun z=>(phi z.1,phi' z.2)) (fun z=>(psi z.1,psi' z.2)) k hParamChart hProduct.
exists [set z:V*W|T z.1 /\T' z.2],
  (fun u=>U (eRS u).1 /\U' (eRS u).2),
  (fun z=>pRS (phi z.1,phi' z.2)),(fun u=>(psi (eRS u).1,psi' (eRS u).2)).
split.
- have hPoint:T a.1 /\T' a.2.
    split.
    + exact (norm_domain_interior_member (inner_norm_real_norm hV) hBase).
    + exact (norm_domain_interior_member (inner_norm_real_norm hW) hBase').
  exact ((norm_class_continuous (norm_coordinate_class_forward hCoordinates) hPoint).1).
- split; last exact hCoordinates.
  exact (@inner_convex_linear_inverse_image R (R_n R (r+s))
    [the lmodType R of (R_n R r*R_n R s)%type] _ eRS (inner_cartesian_convex hConv hConv')).
Qed.
