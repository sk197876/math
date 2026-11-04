(** Federer (1969), 3.2.48, p. 286: right multiplication by an
    actual isotropy inverse retains Phi(y) and transforms the original
    tangent word by the corresponding orthogonal transverse action. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  OrthogonalMaps ExteriorGrading ExteriorMaps ExteriorNorm ExteriorNormNaturality
  AssociatedSubspace AssociatedSubspaceIsomorphism SimpleElementary
  SphericalCoordinateIsotropy SphericalOrthogonalProductAlgebra SphericalProductPreimageImage
  SphericalTangentCoordinates SphericalIsotropyTransverseAction TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_right_inverse_preimage]:
    Phi(y h inverse)=Phi(y) in 3.2.48, p. 286. The actual
    preimage set is invariant, with the original subset retained. *)
Theorem spherical_isotropy_right_inverse_preimage (R:realType) d (c:R_n R (1+d))
    (Q y:Hom (R_n R (1+d)) (R_n R (1+d)))
    (h:Hom (R_n R d) (R_n R d)) (B:set (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->Q (spherical_coordinate_pole R d)=c ->
  is_orthogonal_map (@euclidean_inner_product R d) (@euclidean_inner_product R d) (hom_as_linear h) ->
  spherical_orthogonal_preimage c B y ->
  let y':=hom_comp y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)) in
  spherical_orthogonal_preimage c B y' /\y' c=y c.
Proof.
move=>hQ hQc hh hy y'.
have hMember:=@spherical_isotropy_transverse_operator_member R d Q h hQ hh.
rewrite hQc in hMember.
have hInvPole:euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h) c=c.
  have hFixed:=congr1 (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)) hMember.2.
  rewrite (euclidean_orthogonal_adjoint_cancel hMember.1) in hFixed; exact (esym hFixed).
have hValue:y' c=y c by change (y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h) c)=y c); rewrite hInvPole.
split; last exact hValue.
split.
- move=>u v; change (euclidean_inner_product
    (y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h) u))
    (y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h) v))=euclidean_inner_product u v).
  by rewrite hy.1 (euclidean_orthogonal_adjoint_orthogonal hMember.1).
- by rewrite hValue; exact hy.2.
Qed.

(** Source for [spherical_isotropy_translated_tangent_word]: the
    actual T(y h inverse)=h T(y) and transformed unit word in
    3.2.48, p. 286. Both associated planes refer to the original
    tangent at the unchanged base point. No orientation sign is chosen. *)
Theorem spherical_isotropy_translated_tangent_word (R:realType) d m
    (c:R_n R (1+d)) (Q y:Hom (R_n R (1+d)) (R_n R (1+d)))
    (h:Hom (R_n R d) (R_n R d)) (B:set (R_n R (1+d)))
    (tau:exterior_power (R_n R d) m):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->Q (spherical_coordinate_pole R d)=c ->
  is_orthogonal_map (@euclidean_inner_product R d) (@euclidean_inner_product R d) (hom_as_linear h) ->
  spherical_orthogonal_preimage c B y ->
  (forall u,FedererSimple.T tau u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
    B (y c) (y (spherical_transverse_embedding Q u))) ->
  let y':=hom_comp y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)) in
  forall u,FedererSimple.T (exterior_power_map (hom_as_linear h) m tau) u <->
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
      B (y' c) (y' (spherical_transverse_embedding Q u)).
Proof.
move=>hQ hQc hh hy hTau y' u.
have [_ hPole]:=@spherical_isotropy_right_inverse_preimage R d c Q y h B hQ hQc hh hy.
have hAssociated:=@associated_subspace_isomorphism R (R_n R d) (R_n R d)
  (hom_as_linear h) (hom_as_linear (euclidean_rectangular_adjoint h)) m tau
  (euclidean_orthogonal_adjoint_cancel hh) (euclidean_orthogonal_adjoint_cancel_reverse hh) u.
rewrite hAssociated hTau hPole.
have hAction:=@spherical_isotropy_transverse_inverse_action R d Q h hQ hh u.
have hValue:y' (spherical_transverse_embedding Q u)=
    y (spherical_transverse_embedding Q (euclidean_rectangular_adjoint h u)).
  change (y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)
    (spherical_transverse_embedding Q u))=y (spherical_transverse_embedding Q (euclidean_rectangular_adjoint h u))).
  by rewrite hAction.
by rewrite hValue.
Qed.
