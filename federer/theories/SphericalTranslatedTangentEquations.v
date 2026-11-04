(** Federer (1969), 3.2.48, p. 285: exact equations for the original
    tangent spaces after inverse left translation. Actual group tangent
    transport and the original preimage tangent theorem discharge the laws
    needed by the local isometric charts. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse EuclideanGramDifferentialAlgebra
  SphericalOrthogonalTangents SphericalOrthogonalTangentTranslation
  SphericalOrthogonalPreimageTangent SphericalProductPreimageImage
  EuclideanSubmanifoldUP UnitSphereSpace TangentConeUP SphericalTangentCoordinates
  SphericalCoordinateIsotropy SphericalHorizontalSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_group_tangent_inverse_translate]: the left
    group tangent arrow of the actual differential diagram, 3.2.48,
    p. 285, using Tan(O,g)=g Tan(O,1) from 3.2.47, p. 283. *)
Lemma spherical_group_tangent_inverse_translate (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  (norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set h|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear h)] g w <->
    euclidean_gram_differential (hom_of_linear (linear_id (R_n R N)))
      (hom_comp (euclidean_rectangular_adjoint g) w)=0).
Proof.
move=>hg.
pose idV:Hom (R_n R N) (R_n R N):=hom_of_linear (linear_id (R_n R N)).
have hId:is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear idV) by move=>x y.
rewrite (spherical_orthogonal_tangent_left_translate hg).
split.
- move=>[u hu hgu].
  have hInverse:hom_comp (euclidean_rectangular_adjoint g) w=u.
    rewrite -hgu; apply:hom_ext=>v.
    exact (euclidean_orthogonal_adjoint_cancel hg (u v)).
  rewrite hInverse; move:hu; by rewrite (spherical_orthogonal_tangent_gram hId).
- move=>hw; exists (hom_comp (euclidean_rectangular_adjoint g) w).
  + by rewrite (spherical_orthogonal_tangent_gram hId).
  + apply:hom_ext=>v; exact (euclidean_orthogonal_adjoint_cancel_reverse hg (w v)).
Qed.

(** Source for [spherical_preimage_translated_tangent_equations]: the
    actual tangent inverse image in the two source rows of 3.2.48,
    p. 285. The horizontal plane law refers to the original manifold
    tangent at g(c), with the exact transverse coordinates retained. *)
Theorem spherical_preimage_translated_tangent_equations (R:realType) d r
    (c:R_n R (1+d)) (E:set (R_n R (1+d)))
    (g Q:Hom (R_n R (1+d)) (R_n R (1+d))) (S:set (R_n R d)):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  @is_euclidean_submanifold R (1+d)%N r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R (1+d) ->
  spherical_orthogonal_preimage c E g ->
  (forall u,S u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
    E (g c) (g (spherical_transverse_embedding Q u))) ->
  forall w,
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c E) g w <->
    euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d))))
      (hom_comp (euclidean_rectangular_adjoint g) w)=0 /\
    S (spherical_transverse_coordinates Q ((hom_comp (euclidean_rectangular_adjoint g) w) c)).
Proof.
move=>hc hQ hQc hMan hSphere hg hS w.
have hPre:=@spherical_orthogonal_preimage_tangent R d r c E g hc hMan hSphere hg.
rewrite hPre /set_of.
pose idV:Hom (R_n R (1+d)) (R_n R (1+d)):=hom_of_linear (linear_id (R_n R (1+d))).
pose w0:=hom_comp (euclidean_rectangular_adjoint g) w.
have hRestore:euclidean_gram_differential idV w0=0 ->
    g (spherical_transverse_embedding Q (spherical_transverse_coordinates Q (w0 c)))=w c.
  move=>hw.
  have hPerp:=@spherical_gram_tangent_evaluation_perpendicular R (1+d) idV w0 c hw.
  have hJ:spherical_transverse_embedding Q (spherical_transverse_coordinates Q (w0 c))=w0 c.
    apply:(spherical_transverse_coordinates_inverse hQ); by rewrite hQc.
  rewrite hJ; exact (euclidean_orthogonal_adjoint_cancel_reverse hg.1 (w c)).
split.
- move=>[hw hOther].
  have hw0:euclidean_gram_differential idV w0=0:=
    (spherical_group_tangent_inverse_translate w hg.1).1 hw.
  split; first exact hw0.
  apply:(hS _).2; by rewrite (hRestore hw0).
- move=>[hw hOther]; split.
  + exact ((spherical_group_tangent_inverse_translate w hg.1).2 hw).
  + have h:= (hS _).1 hOther; by rewrite (hRestore hw) in h.
Qed.
