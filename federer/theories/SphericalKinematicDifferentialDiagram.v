(** Federer (1969), 3.2.48, p. 285: commutation of the actual
    differential diagram with the two normalized direct-sum charts.
    The full ambient polynomial differential is used, and the Gram
    equation justifies inversion on the original orthogonal tangents. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm EuclideanHomInnerCharts
  OrthogonalMaps EuclideanGramDifferentialAlgebra EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse SphericalHorizontalLift ProductInner
  NormDifferentialUP TangentConeUP SphericalTranslatedTangentEquations
  SphericalTangentCoordinates SphericalKinematicTargetEmbedding OrthogonalKinematicMap OrthogonalKinematicTangent
  CommonVerticalDifferenceExteriorNorm CartesianTopExteriorNorm CartesianDifferenceExteriorNorm
  CartesianFourFactorShuffle SubspaceDifference ProductInnerDifferential ProductLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_differential_diagram]: the original
    D Psi and conjugated vector subtraction in 3.2.48, p. 285.
    The two chart values are actual Hilbert Hom vectors; the target
    is the normalized common-vertical subtraction, including all kernels. *)
Theorem spherical_kinematic_differential_diagram (R:realType) d (c:R_n R (1+d))
    (Q x y:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))) (S T:subspace (R_n R d)):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear x) ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear y) ->
  (forall w,K w ->euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0) ->
  exists D:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type]
      (Hom (R_n R (1+d)) (R_n R (1+d))),
    has_norm_differential
      (inner_norm (product_inner_productP
        (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
      (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      setT (@orthogonal_kinematic_map R (1+d)) (x,y) D /\
    forall (a:subspace_space K*subspace_space S) (b:subspace_space K*subspace_space T),
      D (hom_comp x (spherical_kinematic_target_embedding_hom c Q K (a.1,subspace_val a.2)),
         hom_comp y (spherical_kinematic_target_embedding_hom c Q K (b.1,subspace_val b.2)))=
      hom_comp x (hom_comp
        (spherical_kinematic_target_embedding_hom c Q K
          (@common_vertical_difference_hom R (subspace_space K) (R_n R d) S T (a,b)))
        (euclidean_rectangular_adjoint y)).
Proof.
move=>hx hy hK.
pose H:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose idV:H:=hom_of_linear (linear_id (R_n R (1+d))).
pose L:=spherical_kinematic_target_embedding_hom c Q K.
have hId:is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear idV) by move=>u v.
have hGram (a:subspace_space K*R_n R d):euclidean_gram_differential idV (L a)=0.
  change (euclidean_gram_differential idV (subspace_val a.1+(Num.sqrt (2:R))^-1*:
    spherical_horizontal_lift idV c (spherical_transverse_embedding Q a.2))=0).
  rewrite linearD linearZ.
  change (euclidean_gram_differential idV (subspace_val a.1)+(Num.sqrt (2:R))^-1*:
    euclidean_gram_differential idV
      (spherical_horizontal_lift idV c (spherical_transverse_embedding Q a.2))=0).
  by rewrite (hK _ (subspace_valP a.1))
    (@spherical_horizontal_lift_tangent R (1+d) idV c (spherical_transverse_embedding Q a.2) hId)
    scaler0 addr0.
have [D [hD hValue]]:=@orthogonal_kinematic_map_differential R (1+d) x y.
exists D; split; first exact hD.
move=>a b.
have hyTan:norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
    [set h|is_orthogonal_map (@euclidean_inner_product R (1+d))
      (@euclidean_inner_product R (1+d)) (hom_as_linear h)] y
    (hom_comp y (L (b.1,subspace_val b.2))).
  apply:(spherical_group_tangent_inverse_translate _ hy).2.
  have hCancel:hom_comp (euclidean_rectangular_adjoint y) (hom_comp y (L (b.1,subspace_val b.2)))=
      L (b.1,subspace_val b.2).
    by apply:hom_ext=>v; exact (euclidean_orthogonal_adjoint_cancel hy _).
  by rewrite hCancel; exact (hGram (b.1,subspace_val b.2)).
rewrite hValue (@orthogonal_kinematic_tangent_formula R (1+d) x y
  (hom_comp x (L (a.1,subspace_val a.2))) (hom_comp y (L (b.1,subspace_val b.2))) hx hy hyTan).
have hCancel (g:H) (hg:is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear g)) (f:H):
    hom_comp (euclidean_rectangular_adjoint g) (hom_comp g f)=f.
  by apply:hom_ext=>v; exact (euclidean_orthogonal_adjoint_cancel hg _).
rewrite (hCancel x hx) (hCancel y hy).
have hDifference:L (@common_vertical_difference_hom R (subspace_space K) (R_n R d) S T (a,b))=
    L (a.1,subspace_val a.2)-L (b.1,subspace_val b.2).
  rewrite -(linB (hom_linear L)).
  congr (L _).
  change (cartesian_linear_hom (@cartesian_difference_hom R (subspace_space K))
    (hom_of_linear (GRing.Linear.clone _ _ _ _ (subspace_difference S T) _))
    ((a.1,b.1),(a.2,b.2))=(a.1,subspace_val a.2)-(b.1,subspace_val b.2)).
  rewrite cartesian_linear_homE cartesian_difference_homE.
  reflexivity.
by rewrite hDifference.
Qed.
