(** Federer (1969), 3.2.47, p. 283: the intersection
    of W(g) with the actual tangent of Phi inverse(E)
    has dimension r. An injective actual horizontal lift of
    Tan(E,Phi(g)) proves existence of the r-plane. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceSums SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates LinearBasis LinearRankUP LinearInjectiveRank
  HomCompositionDeterminant EuclideanInnerProduct InnerNorm OrthogonalMaps EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanSubmanifoldUP SubmanifoldTangentPlane
  TangentConeUP UnitSphereSpace UnitSphereSubsetTangents SphericalHorizontalLift
  SphericalHorizontalLiftLinear SphericalHorizontalSpace SphericalOrthogonalTangents
  SphericalOrthogonalPreimageTangent SphericalProductPreimageImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_horizontal_dimension]: the
    r-dimensional horizontal intersection in the last display of
    3.2.47, p. 283. The original class-one E and
    original g remain; dimension zero is included. *)
Theorem spherical_preimage_horizontal_dimension (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (g:Hom (R_n R n.+1) (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage c E g ->
  exists Z:G (Hom (R_n R n.+1) (R_n R n.+1)) r,
    [set w|spherical_horizontal_space g c w /\
      norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
        (spherical_orthogonal_preimage c E) g w]=(grassmann_val Z:set _).
Proof.
move=>hc hMan hSphere hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R n.+1)) hc expr1n.
have [U hU]:=@submanifold_tangent_plane R n.+1 r 1%N E (g c) (leqnn 1) hMan hg.2.
pose Y:=subspace_space (grassmann_val U).
pose lift0:=fun u:Y=>spherical_horizontal_lift g c (subspace_val u).
have hLinear:linear lift0.
  move=>a u v; exact (@spherical_horizontal_lift_linear R n.+1 g c a
    (subspace_val u) (subspace_val v)).
pose L:Hom Y H:=@HomMap R Y H lift0 (introT (asboolP _) hLinear).
have hPerp v (hv:grassmann_val U v):euclidean_inner_product (g c) v=0.
  apply:(@unit_sphere_subset_tangent_orthogonal R V
    (@euclidean_inner_product R n.+1) (@euclidean_inner_productP R n.+1)
    E (g c) hSphere (hSphere (g c) hg.2) v).
  by rewrite hU.
have hEval u:L u c=subspace_val u.
  exact (@spherical_horizontal_lift_evaluation R n.+1 g c (subspace_val u)
    hUnit (@hPerp _ (subspace_valP u))).
have hInjective:injective L.
  move=>u v h; apply:subspace_val_injective.
  exact (eq_trans (esym (hEval u)) (eq_trans (congr1 (fun w:H=>w c) h) (hEval v))).
have [b hb]:=grassmann_proof U.
pose d:=@hom_rank_one_base R V V n.+1 n.+1 (@coordinate_basis R n.+1)
  (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1).
have hd:is_basis d:=@hom_rank_one_baseP R V V n.+1 n.+1 (@coordinate_basis R n.+1)
  (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1).
have hRank:=@linear_injective_rank R Y H r b hb _ d hd L hInjective.
pose Z:=@GrassmannSubspace R H r (range_subspace (hom_as_linear L)) hRank.
have hTan:=@spherical_orthogonal_preimage_tangent R n r c E g hc hMan hSphere hg.
exists Z; apply/seteqP; split=>w.
- move=>[hw hPre].
  have hValue:grassmann_val U (w c).
    rewrite hTan in hPre; rewrite -hU; exact hPre.2.
  exists (@subspace_lift R V (grassmann_val U) (w c) hValue).
  exact (@spherical_horizontal_lift_characterization R n.+1 g w c hg.1 hUnit hw).
- move=>[u hValue]; change (w=L u) in hValue; rewrite hValue.
  split; first exact (@spherical_horizontal_lift_member R n.+1 g c (subspace_val u) hg.1).
  rewrite hTan; split.
  + rewrite (spherical_orthogonal_tangent_gram hg.1).
    exact (@spherical_horizontal_lift_tangent R n.+1 g c (subspace_val u) hg.1).
  + rewrite hEval hU; exact (subspace_valP u).
Qed.

(** Source for [spherical_preimage_contains_vertical_tangent]:
    the printed ker D Phi(g) subset Tan(Phi inverse(E),g),
    3.2.47, p. 283. The zero vector belongs to the
    original target tangent because Phi(g) belongs to E. *)
Lemma spherical_preimage_contains_vertical_tangent (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (g w:Hom (R_n R n.+1) (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage c E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    [set h|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear h)] g w ->
  w c=0 ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    (spherical_orthogonal_preimage c E) g w.
Proof.
move=>hc hMan hSphere hg hw hZero.
rewrite (@spherical_orthogonal_preimage_tangent R n r c E g hc hMan hSphere hg).
split; first exact hw.
rewrite hZero; move=>eps hEps; exists (g c),1; split; first exact hg.2.
split; first exact:ltr01.
by rewrite subrr scaler0 subr0 inner_norm0; split.
Qed.
