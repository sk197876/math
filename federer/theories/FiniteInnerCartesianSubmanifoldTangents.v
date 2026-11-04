(** Federer (1969), 3.2.48, p. 285: the actual tangent of the
    source product is the product of its manifold tangents. The local
    retractions are proved to exist from 3.1.19(4), p. 231, in the
    original finite inner-product ambient spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom InnerProductUP InnerNorm HilbertFormCompactness
  ProductInner FiniteInnerSubmanifoldUP FiniteInnerSubmanifoldCoordinates
  NormCoordinateSystemUP RetractionUP NormRegularity NormClassOneUP NormDifferentialUP
  TangentConeUP InnerCartesianRetractionTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_submanifold_differentiable_retraction]:
    supporting the two source retractions used for the tangent diagram
    of 3.2.48, p. 285. The actual local coordinate system supplies the
    retraction and its differential; neither is an additional premise. *)
Theorem finite_inner_submanifold_differentiable_retraction (R:realType) (V:lmodType R)
    BV (hV:@is_inner_product R V BV) r (M:set V) a:
  is_inner_submanifold BV r 1%N M ->M a ->
  exists T f (D:Hom V V),
    has_norm_differential (inner_norm hV) (inner_norm hV) T f a D /\
    (forall x,T x ->M (f x)) /\(forall x,M x ->T x ->f x=x).
Proof.
move=>hM ha.
have [T [U [phi [psi [hBase [hConv hCoordinates]]]]]]:=
  @finite_inner_submanifold_coordinates R V BV hV r 1%N M a hM ha.
have hRet:=norm_coordinate_system_retraction hCoordinates.
have [DF hDF]:=(norm_class_firstP _ _ _ _).1 (norm_retraction_class hRet).
have haT:=norm_domain_interior_member (inner_norm_real_norm hV) hBase.
exists T,(fun x=>psi (phi x)),(DF a); split.
- exact (norm_class_one_differential hDF haT).
- split.
  + move=>x hx; exact (norm_retraction_range hRet hx).1.
  + move=>x hx hxT; exact (norm_retraction_fixed hRet (conj hx hxT)).
Qed.

(** Source for [finite_inner_cartesian_submanifold_tangent]: the
    actual top source tangent row of 3.2.48, p. 285. The two actual
    manifold hypotheses discharge the local retraction requirements;
    there is no supplied tangent-product or derivative-field hypothesis. *)
Theorem finite_inner_cartesian_submanifold_tangent (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    r s (M:set V) (N:set W) a b:
  is_inner_submanifold BV r 1%N M ->is_inner_submanifold BW s 1%N N ->M a ->N b ->
  norm_tangent_cone (inner_norm (product_inner_productP hV hW))
    [set z:V*W|M z.1 /\N z.2] (a,b)=
    [set z:V*W|norm_tangent_cone (inner_norm hV) M a z.1 /\
      norm_tangent_cone (inner_norm hW) N b z.2].
Proof.
move=>hM hN ha hb.
have [T [f [D [hD [hRange hFix]]]]]:=
  @finite_inner_submanifold_differentiable_retraction R V BV hV r M a hM ha.
have [U [g [E [hE [hRangeG hFixG]]]]]:=
  @finite_inner_submanifold_differentiable_retraction R W BW hW s N b hN hb.
exact (@inner_cartesian_retraction_tangent R V W BV BW hV hW M T N U f g a b D E
  ha hb hD hE hRange hRangeG hFix hFixG).
Qed.
