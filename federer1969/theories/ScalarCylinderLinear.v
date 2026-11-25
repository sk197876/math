(** Federer (1969), 3.2.33, p. 270: the actual linear
    differential of the cylinder map keeps its first mu coordinates
    and multiplies its next coordinate by g'(x_(mu+1)). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormFiniteLinearBound ScalarCylinderMapUP ScalarCylinderMapExistence
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockNorms EuclideanOneCoordinate EuclideanOneNormDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_linear]: supporting computation
    of Df in Federer 3.2.33, p. 270. A linear
    scalar function gives a linear cylinder map directly from
    its independent coordinate laws, including mu= 0. *)
Lemma scalar_cylinder_linear (R:realType) mu k c
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map (fun t=>c*t) F ->linear F.
Proof.
move=>hF a x y; apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>j.
- by rewrite !ffunE !(scalar_cylinder_first_coordinates hF) !ffunE.
- rewrite (ord1 j) !ffunE !(scalar_cylinder_last_coordinate hF) !ffunE.
  change (c*(a*x (lshift k (rshift mu ord0))+y (lshift k (rshift mu ord0)))=
    a*(c*x (lshift k (rshift mu ord0)))+c*y (lshift k (rshift mu ord0))).
  ring.
Qed.

(** Source for [scalar_cylinder_linear_exists]: the displayed
    differential has an actual bounded linear representative,
    supporting the rank and Jacobian assertions in Federer
    3.2.33, p. 270. Finite-dimensional continuity is proved,
    not an additional differential hypothesis. *)
Lemma scalar_cylinder_linear_exists (R:realType) mu k c:
  exists L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1)),
    is_scalar_cylinder_map (fun t=>c*t) L /\
    norm_bounded_linear (inner_norm (@euclidean_inner_productP R ((mu+1)+k)))
      (inner_norm (@euclidean_inner_productP R (mu+1))) L.
Proof.
have [F hF]:=@scalar_cylinder_map_exists R mu k (fun t=>c*t).
pose L:=@HomMap R (R_n R ((mu+1)+k)) (R_n R (mu+1)) F
  (introT (asboolP _) (scalar_cylinder_linear hF)).
exists L; split; first exact hF.
exact:(@norm_finite_linear_bounded R (R_n R ((mu+1)+k)) (R_n R (mu+1))
  (inner_norm (@euclidean_inner_productP R ((mu+1)+k)))
  (inner_norm (@euclidean_inner_productP R (mu+1)))
  (inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k)))
  (inner_norm_real_norm (@euclidean_inner_productP R (mu+1)))
  ((mu+1)+k) (@coordinate_basis R ((mu+1)+k)) (@coordinate_basisP R ((mu+1)+k)) L).
Qed.

(** Source for [euclidean_last_coordinate_norm]: the norm of
    an error with only its last coordinate nonzero is the
    absolute value of that coordinate, supporting the actual
    differential calculation in Federer 3.2.33, p. 270. *)
Lemma euclidean_last_coordinate_norm (R:realType) mu (u:R_n R (mu+1)):
  (forall i,u (lshift 1 i)= 0) ->
  inner_norm (@euclidean_inner_productP R (mu+1)) u=`|u (rshift mu ord0)|.
Proof.
move=>hZero.
have hEq:u=@euclidean_last_injection R mu 1 (euclidean_one_embed (u (rshift mu ord0))).
  apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>j.
  - by rewrite hZero /euclidean_last_injection euclidean_block_join_left ffunE.
  - by rewrite (ord1 j) /euclidean_last_injection euclidean_block_join_right /euclidean_one_embed ffunE.
by rewrite {1}hEq euclidean_last_injection_norm euclidean_one_norm_coordinate /euclidean_one_embed ffunE.
Qed.
