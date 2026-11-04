(** Federer (1969), 3.1.19(4), p. 231: coordinates
    of a submanifold within a coordinate patch compose to
    actual ambient coordinates. Supporting the reduction by
    3.2.29 in 3.2.47, p. 283: the covering
    manifolds must lie in the original sphere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerConvex HilbertFormCompactness RealNormUP NormDifferentialUP
  NormRegularity NormRegularityOperations NormCoordinateSystemUP
  FiniteInnerChartUP FiniteInnerSubmanifoldUP FiniteInnerCoordinatesSubmanifold
  EuclideanSubmanifoldUP SubmanifoldStraighteningCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_coordinate_image_composition]: composition
    of actual coordinate systems in 3.1.19(4), p. 231,
    supporting the class-one cover within the sphere used
    in 3.2.47, p. 283. The exact image and
    original open parameter domain are retained. *)
Theorem norm_coordinate_image_composition (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (S T:set X) (U M TE:set Y) (Q:set Z)
    (phi:X->Y) (psi:Y->X) (phiM:Y->Z) (psiM:Z->Y) k:
  is_norm_coordinate_system hNX hNY S T U phi psi k ->
  is_norm_coordinate_system hNY hNZ M TE Q phiM psiM k ->M `<=` U ->
  is_norm_coordinate_system hNX hNZ (psi @` M) (fun x=>T x /\TE (phi x)) Q
    (fun x=>phiM (phi x)) (fun z=>psi (psiM z)) k.
Proof.
move=>hC hM hMU.
have hForward:=norm_class_composition (norm_coordinate_class_forward hC) (norm_coordinate_class_forward hM).
have hMap z (hz:Q z):U (psiM z).
  exact:hMU _ (norm_coordinate_backward_membership hM hz).1.
have hBackward:=@norm_class_compose_on R Z Y X NZ NY NX hNZ hNY hNX Q U psiM psi k
  hMap (norm_coordinate_class_backward hM) (norm_coordinate_class_backward hC).
constructor.
- exact hForward.
- exact hBackward.
- move=>x hx; exact (norm_coordinate_forward_range hM hx.2).
- apply/seteqP; split=>x.
  + move=>[z hz <-].
    have hValue:=norm_coordinate_backward_membership hM hz.
    have hAmbient:=norm_coordinate_backward_membership hC (@hMU _ hValue.1).
    split; first by exists (psiM z); first exact hValue.1.
    split; first exact hAmbient.2.
    rewrite (norm_coordinate_cancel hC (@hMU _ hValue.1)); exact hValue.2.
  + move=>[[b hb <-] [hT hTE]].
    have hbU:=hMU b hb.
    have hbTE:TE b by rewrite (norm_coordinate_cancel hC hbU) in hTE.
    exists (phiM b); first exact (norm_coordinate_forward_range hM hbTE).
    by rewrite (norm_coordinate_base_inverse hM hb hbTE).
- move=>z hz.
  rewrite (norm_coordinate_cancel hC (@hMap z hz)).
  exact (norm_coordinate_cancel hM hz).
Qed.

(** Source for [finite_inner_coordinate_submanifold_image_in_chart]:
    actual submanifolds in a parameter open set map to
    actual ambient submanifolds by a coordinate inverse,
    by 3.1.19, p. 231. Supporting 3.2.47,
    p. 283, the image remains within the original
    containing manifold, with no assumed rank or openness. *)
Theorem finite_inner_coordinate_submanifold_image_in_chart (R:realType) (X:lmodType R)
    BX (hX:@is_inner_product R X BX) N (e:Hom (R_n R N) X) (p:Hom X (R_n R N))
    d r k (S T:set X) (U M:set (R_n R d)) (phi:X->R_n R d) (psi:R_n R d->X):
  (1<=k)%N ->is_finite_inner_chart BX e p ->
  is_norm_coordinate_system (inner_norm_real_norm hX)
    (inner_norm_real_norm (@euclidean_inner_productP R d)) S T U phi psi k ->
  @is_euclidean_submanifold R d r k M ->M `<=` U ->
  @is_euclidean_submanifold R N r k (p @` (psi @` M)).
Proof.
move=>hk hChart hC hMan hMU.
pose hNX:=inner_norm_real_norm hX.
pose hND:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose hNR:=inner_norm_real_norm (@euclidean_inner_productP R r).
apply:(@finite_inner_coordinates_euclidean_submanifold R X BX hX N e p r k (psi @` M) hk hChart).
move=>a [b hb <-].
have [TE [Q [phiM [psiM [hBase [hConv [hPhi [hPsi [hRange [_ [hImage hCancel]]]]]]]]]]]:=
  @submanifold_convex_coordinates R d r k M hMan b hb.
have hCM:is_norm_coordinate_system hND hNR M TE Q phiM psiM k by constructor.
have hComposed:=@norm_coordinate_image_composition R X (R_n R d) (R_n R r)
  _ _ _ hNX hND hNR S T U M TE Q phi psi phiM psiM k hC hCM hMU.
exists (fun x=>T x /\TE (phi x)),Q,(fun x=>phiM (phi x)),(fun z=>psi (psiM z)).
split.
- have hPoint:T (psi b) /\TE (phi (psi b)).
    split; first exact (norm_coordinate_backward_membership hC (@hMU b hb)).2.
    rewrite (norm_coordinate_cancel hC (@hMU b hb)).
    exact (norm_domain_interior_member hND hBase).
  exact ((@norm_class_continuous R X (R_n R r) _ _ hNX hNR _ _ k
    (norm_coordinate_class_forward hComposed) (psi b) hPoint).1).
- split; [exact hConv|exact hComposed].
Qed.

(** Source for [euclidean_coordinate_submanifold_image]:
    actual submanifolds map to actual submanifolds through
    coordinate inverses in 3.1.19, p. 231,
    supporting the sphere-contained cover of 3.2.47,
    p. 283. The identity ambient chart introduces
    no new geometric hypothesis. *)
Corollary euclidean_coordinate_submanifold_image (R:realType) N d r k
    (S T:set (R_n R N)) (U M:set (R_n R d))
    (phi:R_n R N->R_n R d) (psi:R_n R d->R_n R N):
  (1<=k)%N ->
  is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R N))
    (inner_norm_real_norm (@euclidean_inner_productP R d)) S T U phi psi k ->
  @is_euclidean_submanifold R d r k M ->M `<=` U ->
  @is_euclidean_submanifold R N r k (psi @` M).
Proof.
move=>hk hC hMan hMU.
pose X:=R_n R N.
pose idX:Hom X X:=hom_of_linear (TensorUP.linear_id X).
have hChart:is_finite_inner_chart (@euclidean_inner_product R N) idX idX by constructor.
have hResult:=@finite_inner_coordinate_submanifold_image_in_chart R X _
  (@euclidean_inner_productP R N) N idX idX d r k S T U M phi psi hk hChart hC hMan hMU.
have hImage:idX @` (psi @` M)=psi @` M.
  apply/seteqP; split=>x; first by move=>[y hy <-].
  by move=>hx; exists x.
by rewrite hImage in hResult.
Qed.
