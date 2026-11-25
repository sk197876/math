(** Federer (1969), 3.2.48, p. 286: the actual
    isotropy acts by the whole orthogonal group on the
    tangent hyperplane. Local transverse coordinates identify each
    actual stabilizer action with its original O(d) operator;
    the block extension is used through its sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct OrthogonalMaps
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanBlockExtensionUP EuclideanBlockExtension
  SphericalCoordinateIsotropy SphericalIsotropyConjugacy SphericalOrthogonalProductAlgebra
  SphericalTangentCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_isotropy_transverse_operator]: supporting
    actual stabilizer operator Q diag(1,h) Q inverse
    in 3.2.48, p. 286. Q remains a local
    frame parameter, and the transverse extension is the
    existing sealed map specified by its block-action law. *)
Definition spherical_isotropy_transverse_operator (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))) (h:Hom (R_n R d) (R_n R d)):=
  spherical_isotropy_conjugate Q
    (hom_of_linear (@euclidean_block_extension R 1 d (hom_as_linear h))).

(** Source for [spherical_isotropy_transverse_operator_member]: every
    actual h in O(d) gives an actual stabilizer
    element, supporting the Haar average in 3.2.48,
    p. 286. Membership and the fixed original pole
    are proved, rather than assumed action laws. *)
Lemma spherical_isotropy_transverse_operator_member (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))) (h:Hom (R_n R d) (R_n R d)):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R d) (hom_as_linear h) ->
  spherical_orthogonal_isotropy (Q (spherical_coordinate_pole R d))
    (spherical_isotropy_transverse_operator Q h).
Proof.
move=>hQ hh; apply:(spherical_isotropy_conjugacy_member hQ).
exact (@spherical_coordinate_extension_member R d h hh).
Qed.

(** Source for [spherical_isotropy_transverse_action]: supporting
    the actual transverse action in 3.2.48, p. 286:
    the stabilizer operator on J(u) equals J(h(u)).
    This holds even before requiring h orthogonal. *)
Lemma spherical_isotropy_transverse_action (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))) (h:Hom (R_n R d) (R_n R d)):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->forall u,
  spherical_isotropy_transverse_operator Q h (spherical_transverse_embedding Q u)=
    spherical_transverse_embedding Q (h u).
Proof.
move=>hQ u.
change (Q (@euclidean_block_extension R 1 d (hom_as_linear h)
  (euclidean_rectangular_adjoint Q (Q (@euclidean_last_injection R 1 d u))))=
  Q (@euclidean_last_injection R 1 d (h u))).
rewrite (euclidean_orthogonal_adjoint_cancel hQ).
congr (Q _).
exact (@euclidean_block_extension_specification R 1 d (hom_as_linear h) 0 u).
Qed.

(** Source for [spherical_isotropy_transverse_inverse_action]: the
    inverse actual stabilizer acts in transverse coordinates
    by h inverse, supporting T(y h inverse)=h T(y)
    in 3.2.48, p. 286. Both actual inverses
    are their proved orthogonal adjoints. *)
Lemma spherical_isotropy_transverse_inverse_action (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))) (h:Hom (R_n R d) (R_n R d)):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R d) (hom_as_linear h) ->forall u,
  euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)
    (spherical_transverse_embedding Q u)=
  spherical_transverse_embedding Q (euclidean_rectangular_adjoint h u).
Proof.
move=>hQ hh u.
have hMember:=@spherical_isotropy_transverse_operator_member R d Q h hQ hh.
have hValue:=@spherical_isotropy_transverse_action R d Q h hQ
  (euclidean_rectangular_adjoint h u).
rewrite (euclidean_orthogonal_adjoint_cancel_reverse hh) in hValue.
have hInverseValue:=congr1 (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)) hValue.
rewrite (euclidean_orthogonal_adjoint_cancel hMember.1) in hInverseValue.
exact (esym hInverseValue).
Qed.
