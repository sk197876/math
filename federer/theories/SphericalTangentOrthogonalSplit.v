(** Federer (1969), 3.2.48, p. 285: actual vertical
    and horizontal orthogonal splitting in the differential diagram.
    The existing rank-one lift and Gram tangent equation prove
    the decomposition, rather than assuming an adapted splitting. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm EuclideanHomInnerCharts OrthogonalMaps
  EuclideanGramDifferentialAlgebra SphericalHorizontalLift SphericalHorizontalSpace
  SphericalOrthogonalTangents SphericalProductPreimageImage
  SphericalOrthogonalPreimageTangent EuclideanSubmanifoldUP UnitSphereSpace
  TangentConeUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_gram_tangent_orthogonal_split]: supporting
    the actual direct-sum rows of 3.2.48, p. 285.
    Every original Gram tangent is its vertical residual plus
    the actual horizontal lift of w(c); the two terms
    are orthogonal in the original Hilbert Hom inner product. *)
Theorem spherical_gram_tangent_orthogonal_split (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  inner_norm (@euclidean_inner_productP R N) c= 1 ->
  euclidean_gram_differential g w=0 ->
  exists z:Hom (R_n R N) (R_n R N),
    euclidean_gram_differential g z=0 /\z c=0 /\
    w=z+spherical_horizontal_lift g c (w c) /\
    euclidean_hom_inner_product z (spherical_horizontal_lift g c (w c))=0.
Proof.
move=>hg hc hw.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R N)) hc expr1n.
have hPerp:=@spherical_gram_tangent_evaluation_perpendicular R N g w c hw.
pose horizontal:=spherical_horizontal_lift g c (w c).
pose z:=w-horizontal.
have hGram:euclidean_gram_differential g z=0.
  rewrite /z linearB.
  change (euclidean_gram_differential g w-euclidean_gram_differential g horizontal=0).
  by rewrite hw /horizontal (@spherical_horizontal_lift_tangent R N g c (w c) hg) subrr.
have hZero:z c=0.
  change (w c-spherical_horizontal_lift g c (w c) c=0).
  by rewrite (@spherical_horizontal_lift_evaluation R N g c (w c) hUnit hPerp) subrr.
exists z; split; first exact hGram.
split; first exact hZero.
split; first by rewrite /z subrK.
rewrite (inner_symmetric (@euclidean_hom_inner_productP R N N))
  (@spherical_horizontal_lift_pairing R N g z c (w c) hg hGram) hZero
  (bil0r (inner_bilinear (@euclidean_inner_productP R N))) mulr0.
reflexivity.
Qed.

(** Source for [spherical_preimage_vertical_residual]: the actual
    vertical component remains in Tan(Phi inverse(E),g),
    supporting the preimage direct sum in 3.2.48,
    p. 285. The original class-one E and its
    original tangent are used; no additional plane is assumed. *)
Lemma spherical_preimage_vertical_residual (R:realType) d r
    (c:R_n R d.+1) (E:set (R_n R d.+1))
    (g w:Hom (R_n R d.+1) (R_n R d.+1)):
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  @is_euclidean_submanifold R d.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R d.+1 ->
  spherical_orthogonal_preimage c E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R d.+1 d.+1))
    (spherical_orthogonal_preimage c E) g w ->
  exists z:Hom (R_n R d.+1) (R_n R d.+1),
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R d.+1 d.+1))
      (spherical_orthogonal_preimage c E) g z /\z c=0 /\
    w=z+spherical_horizontal_lift g c (w c) /\
    euclidean_hom_inner_product z (spherical_horizontal_lift g c (w c))=0.
Proof.
move=>hc hMan hSphere hg hw.
have hTan:=@spherical_orthogonal_preimage_tangent R d r c E g hc hMan hSphere hg.
rewrite hTan in hw.
have hGram:euclidean_gram_differential g w=0.
  move:hw.1; by rewrite (spherical_orthogonal_tangent_gram hg.1).
have [z [hzG [hzC [hSum hOrth]]]]:=@spherical_gram_tangent_orthogonal_split R d.+1 g w c hg.1 hc hGram.
exists z; split.
- rewrite hTan; split.
  + by rewrite (spherical_orthogonal_tangent_gram hg.1).
  + rewrite hzC; move=>eps hEps; exists (g c),1; split; first exact hg.2.
    split; first exact:ltr01.
    by rewrite subrr scaler0 subr0 inner_norm0; split.
- by repeat split.
Qed.
