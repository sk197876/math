(** Federer (1969), 3.2.47, p. 283: the actual
    tangent cones of the orthogonal group and sphere, and
    surjectivity of the horizontal differential onto the actual
    sphere tangent. The established Gram tangent theorem and
    rank-one lift prove these geometric identifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness OrthogonalMaps
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra
  EuclideanStiefelTangent UnitSphereSpace UnitSphereSubsetTangents
  TangentConeUP TangentConeBasic TangentDifferentialImage
  SphericalHorizontalLift SphericalHorizontalSpace SphericalTangentEvaluationBound
  SphericalOrthogonalOrbitDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_tangent_gram]: the actual
    group tangent is precisely its Gram differential kernel,
    by 3.2.28(1), p. 263, as recalled in
    the first paragraph of 3.2.47, p. 283. *)
Theorem spherical_orthogonal_tangent_gram (R:realType) N
    (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set h|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear h)] g=
    [set w|euclidean_gram_differential g w=0].
Proof.
move=>hg; rewrite (@euclidean_stiefel_tangent R N N g hg).
apply/seteqP; split=>w hw.
- exact (eq_trans (@euclidean_gram_differentialE R N N g w) hw).
- exact (eq_trans (esym (@euclidean_gram_differentialE R N N g w)) hw).
Qed.

(** Source for [euclidean_unit_sphere_tangent_hyperplane]: the
    actual tangent Tan(Sphere,a) is the perpendicular hyperplane
    to a, as used in 3.2.47, p. 283. Reverse
    inclusion follows by the actual group tangent and evaluation
    differential, rather than an assumed sphere tangent law. *)
Theorem euclidean_unit_sphere_tangent_hyperplane (R:realType) N (a:R_n R N):
  inner_norm (@euclidean_inner_productP R N) a= 1 ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R N))
    (@euclidean_unit_sphere_set R N) a=[set v|euclidean_inner_product a v=0].
Proof.
move=>ha.
pose V:=R_n R N.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R N.
pose hH:=@euclidean_hom_inner_productP R N N.
pose O:set H:=[set g|is_orthogonal_map (@euclidean_inner_product R N)
  (@euclidean_inner_product R N) (hom_as_linear g)].
pose idV:Hom V V:=hom_of_linear (linear_id V).
have hId:O idV by move=>x y.
apply/seteqP; split=>v.
- exact:(@unit_sphere_subset_tangent_orthogonal R V (@euclidean_inner_product R N) hV
    (@euclidean_unit_sphere_set R N) a (fun y hy=>hy) ha v).
- move=>hv.
  pose w:=spherical_horizontal_lift idV a v.
  have hw:norm_tangent_cone (inner_norm hH) O idV w.
    rewrite (@spherical_orthogonal_tangent_gram R N idV hId).
    exact (@spherical_horizontal_lift_tangent R N idV a v hId).
  have hDifferential:=@spherical_orthogonal_orbit_differential R N a idV.
  have hImage:=@norm_differential_tangent_image R H V (inner_norm hH) (inner_norm hV)
    (inner_norm_real_norm hH) (inner_norm_real_norm hV) setT O
    (spherical_orthogonal_orbit a) idV (spherical_orthogonal_orbit a) hDifferential w hw.
  have hSubset:(spherical_orthogonal_orbit a @` (O `&` setT)) `<=`
      @euclidean_unit_sphere_set R N.
    move=>y [g [hg _] <-].
    change (inner_norm hV (g a)= 1).
    by rewrite (orthogonal_map_norm hV hV hg) ha.
  have hResult:=@norm_tangent_mono R V (inner_norm hV) _ _ a hSubset (w a) hImage.
  have hUnit:euclidean_inner_product a a= 1.
    by rewrite -(inner_norm_sqr hV) ha expr1n.
  have hValue:w a=v.
    exact (@spherical_horizontal_lift_evaluation R N idV a v hUnit hv).
  by rewrite hValue in hResult.
Qed.

(** Source for [spherical_horizontal_differential_onto]: D Phi
    maps the actual W(g) onto the actual sphere tangent,
    3.2.47, p. 283. No target tangent or rank
    hypothesis is added beyond membership in that original tangent. *)
Theorem spherical_horizontal_differential_onto (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  inner_norm (@euclidean_inner_productP R N) c= 1 ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R N))
    (@euclidean_unit_sphere_set R N) (g c) v ->
  exists w,spherical_horizontal_space g c w /\w c=v.
Proof.
move=>hg hc hv.
have hgc:inner_norm (@euclidean_inner_productP R N) (g c)= 1.
  by rewrite (orthogonal_map_norm (@euclidean_inner_productP R N)
    (@euclidean_inner_productP R N) hg) hc.
rewrite (euclidean_unit_sphere_tangent_hyperplane hgc) in hv.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R N)) hc expr1n.
exists (spherical_horizontal_lift g c v); split.
- exact (@spherical_horizontal_lift_member R N g c v hg).
- exact (@spherical_horizontal_lift_evaluation R N g c v hUnit hv).
Qed.

(** Source for [spherical_actual_tangent_evaluation_bound]:
    evaluation has norm at most 2^(-1/2) on every
    actual group tangent, supporting the arbitrary-source lower
    mass comparison of 3.2.47(3), p. 283. *)
Theorem spherical_actual_tangent_evaluation_bound (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  inner_norm (@euclidean_inner_productP R N) c= 1 ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set h|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear h)] g w ->
  inner_norm (@euclidean_inner_productP R N) (w c)<=
    (Num.sqrt (2:R))^-1*inner_norm (@euclidean_hom_inner_productP R N N) w.
Proof.
move=>hg hc hw.
rewrite (spherical_orthogonal_tangent_gram hg) in hw.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R N)) hc expr1n.
exact (@spherical_tangent_evaluation_norm_bound R N g w c hg hUnit hw).
Qed.
