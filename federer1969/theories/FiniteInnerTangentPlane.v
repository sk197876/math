(** Federer (1969), 3.1.21, p. 234, used in 3.2.28,
    pp. 264–267: the actual tangent to a class-one
    submanifold has its stated dimension, independently
    of the suitable finite inner-product ambient coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct LinearBasis
  InnerProductUP InnerNorm HilbertFormCompactness NormDifferentialUP
  NormLinearIsometryInverse NormLinearIsomorphismTangent TangentConeUP
  FiniteInnerChartUP FiniteInnerSubmanifoldUP SubmanifoldTangentPlane
  GrassmannInjectiveImage LinearRankUP LinearInjectiveRank LinearRankTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_submanifold_tangent_plane]:
    the dimension of the actual tangent in Federer
    3.2.28, pp. 264–267, by 3.1.21, p. 234.
    The plane is obtained through proved isometric
    coordinates, not postulated as a tangent axiom. *)
Theorem finite_inner_submanifold_tangent_plane (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    mu k (S:set V) a:
  (1<=k)%N ->is_inner_submanifold B mu k S ->S a ->
  exists W:G V mu,norm_tangent_cone (inner_norm hB) S a=(grassmann_val W:set V).
Proof.
move=>hk [d [e [p [hChart hS]]]] ha.
pose X:=R_n R d.
pose NX:=inner_norm (@euclidean_inner_productP R d).
pose NY:=inner_norm hB.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose hNY:=inner_norm_real_norm hB.
have hPa:(p @` S) (p a) by exists a.
have [Z hZ]:=@submanifold_tangent_plane R d mu k (p @` S) (p a) hk hS hPa.
have hEB:norm_bounded_linear NX NY e.
  apply:norm_linear_isometry_bounded=>x.
  exact:(@finite_inner_chart_norm R V B hB d e p hChart x).
have hPB:norm_bounded_linear NY NX p.
  apply:norm_linear_isometry_bounded=>x.
  exact:(@finite_inner_chart_inverse_norm R V B hB d e p hChart x).
have hES:e @` (p @` S)=S.
  apply/seteqP; split=>x.
  - move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hx; exists (p x); last exact:finite_inner_chart_right_inverse hChart x.
    by exists x.
have hT:=@norm_linear_isomorphism_tangent_image R X V NX NY hNX hNY
  e p (p @` S) (p a) hEB hPB (finite_inner_chart_left_inverse hChart)
  (finite_inner_chart_right_inverse hChart).
rewrite hES (finite_inner_chart_right_inverse hChart) hZ in hT.
have [W hW]:=@grassmann_injective_image R X V mu Z e n b hb
  (can_inj (finite_inner_chart_left_inverse hChart)).
exists W; by rewrite hW hT.
Qed.

(** Source for [finite_inner_submanifold_tangent_parameter_rank]:
    every linear parametrisation of the full tangent by
    R^mu is of rank mu, supporting Federer 3.2.28(4),
    p. 266, by 3.1.21, p. 234, and 1.6.1,
    p. 23. The conclusion is proved from the actual range. *)
Theorem finite_inner_submanifold_tangent_parameter_rank (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    mu k (S:set V) a (J:Hom (R_n R mu) V):
  (1<=k)%N ->is_inner_submanifold B mu k S ->S a ->
  norm_tangent_cone (inner_norm hB) S a=range J ->has_linear_rank J mu.
Proof.
move=>hk hS ha hJ.
have [W hW]:=@finite_inner_submanifold_tangent_plane R V B hB n b hb mu k S a hk hS ha.
have [w hw]:=grassmann_proof W.
pose T:=grassmann_val W.
pose L:=hom_of_linear (subspace_inclusion T).
have hL:has_linear_rank L mu:=@linear_injective_rank R (subspace_space T) V
  mu w hw n b hb L (@subspace_val_injective R V T).
apply:(@linear_same_image_rank R (subspace_space T) (R_n R mu) V L J n b hb mu hL).
- move=>t.
  have ht:(range J) (subspace_val t).
    rewrite -hJ hW; exact:subspace_valP t.
  have [z _ hz]:=ht; by exists z.
- move=>z.
  have ht:T (J z).
    have hi:(range J) (J z) by exists z.
    by rewrite -hJ hW in hi.
  exists (@subspace_lift R V T (J z) ht); reflexivity.
Qed.
