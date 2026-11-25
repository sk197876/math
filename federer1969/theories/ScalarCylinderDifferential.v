(** Federer (1969), 3.2.33, p. 270: prove the actual
    differential on the whole original cube from the scalar
    derivative, without assuming a differential field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP RealOpenIntervals
  EuclideanCoordinateMetric EuclideanOpenUnitCube ScalarCylinderMapUP ScalarCylinderLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_actual_differential]: the
    ordinary differential of the printed smooth map in Federer
    3.2.33, p. 270. Its first mu coordinates are the
    identity and its next is g'(x_(mu+1)) times the next
    source coordinate. The remainder is exactly one scalar
    remainder. The source includes every cube point, both zero
    blocks and the actual derivative of g on T. *)
Theorem scalar_cylinder_actual_differential (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)) x c:
  is_scalar_cylinder_map g F ->euclidean_open_unit_cube x ->
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (real_open_interval 0 1) g
    (x (lshift k (rshift mu ord0))) (@scalar_coefficient_linear_map R R^o c) ->
  exists L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1)),
    is_scalar_cylinder_map (fun t=>c*t) L /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R ((mu+1)+k)))
      (inner_norm (@euclidean_inner_productP R (mu+1))) (@euclidean_open_unit_cube R ((mu+1)+k)) F x L.
Proof.
move=>hF hx hG.
have [L [hL hBound]]:=@scalar_cylinder_linear_exists R mu k c.
exists L; split; first exact hL.
constructor.
- exact:(euclidean_open_unit_cube_interior hx).
- exact hBound.
- move=>e he; have [d [hd hRem]]:=norm_differential_remainder hG he.
  exists d; split; first exact hd.
  move=>h hCube hSmall.
  have hScalarSmall:`|h (lshift k (rshift mu ord0))|<d.
    exact:(le_lt_trans (euclidean_coordinate_norm_bound _ h) hSmall).
  have hDomain:real_open_interval 0 1
      (x (lshift k (rshift mu ord0))+h (lshift k (rshift mu ord0))).
    have hh:=hCube (lshift k (rshift mu ord0)); rewrite ffunE in hh.
    by have /andP [h0 h1]:=hh; split.
  have hR:=hRem (h (lshift k (rshift mu ord0))) hDomain hScalarSmall.
  change (is_true (`|g (x (lshift k (rshift mu ord0))+h (lshift k (rshift mu ord0)))-
    g (x (lshift k (rshift mu ord0)))-h (lshift k (rshift mu ord0))*c|<=e*`|h (lshift k (rshift mu ord0))|)) in hR.
  rewrite [h (lshift k (rshift mu ord0))*c]mulrC in hR.
  have hZero i:(F (x+h)-F x-L h) (lshift 1 i)= 0.
    rewrite !ffunE !(scalar_cylinder_first_coordinates hF) (scalar_cylinder_first_coordinates hL) !ffunE.
    ring.
  rewrite (euclidean_last_coordinate_norm hZero) !ffunE
    !(scalar_cylinder_last_coordinate hF) (scalar_cylinder_last_coordinate hL) !ffunE.
  apply:le_trans hR _.
  exact:(ler_wpM2l (ltW he) (euclidean_coordinate_norm_bound _ h)).
Qed.
