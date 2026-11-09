(** Federer (1969), 3.3.4, pp. 290–291:
    the actual inverse active extension
    extends the actual inverse on X.
    Orthogonal inverses are the already
    sealed adjoints of 1.7.4, p. 30. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  EuclideanInjectionRetraction InjectionExtension EuclideanInjectionExtension
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Inverse.
Variable R:realType.
Variables d n:nat.
Variable w:Hom (R_n R d) (R_n R n).
Hypothesis hW:is_orthogonal_map (@euclidean_inner_product R d)
  (@euclidean_inner_product R n) (hom_as_linear w).
Local Notation q:=(euclidean_rectangular_adjoint w).
Local Notation hCancel:=(euclidean_orthogonal_injection_adjoint_cancel hW).

(** Source for [euclidean_injection_extension_adjoint]:
    the inverse active-coordinate extension
    in Federer 3.3.4, pp. 290–291,
    is the extension of the actual
    inverse active operator. Both cancellation
    laws are proved for the original
    opaque extension, with no formula unfolded. *)
Theorem euclidean_injection_extension_adjoint (h:euclidean_orthogonal_group R d):
  euclidean_rectangular_adjoint (injection_extension hCancel (orthogonal_element_map h))=
    injection_extension hCancel (euclidean_rectangular_adjoint (orthogonal_element_map h)).
Proof.
pose H:=injection_extension hCancel (orthogonal_element_map h).
have hH:=euclidean_injection_extension_orthogonality hW h.
have hRight:=euclidean_orthogonal_adjoint_cancel_reverse hH.
have hSmall:=euclidean_orthogonal_adjoint_cancel (orthogonal_element_orthogonal h).
have hLeft:=injection_extension_inverse hCancel hSmall.
apply:hom_ext=>x.
have hPoint:=hLeft (euclidean_rectangular_adjoint H x).
rewrite hRight in hPoint; exact:esym hPoint.
Qed.

(** Source for [euclidean_injection_extension_adjoint_projection]:
    projecting an actual inverse-extended
    vector gives h inverse applied to
    its actual projection, supporting the
    I_j projective-ball computation in
    Federer 3.3.4, p. 291. *)
Theorem euclidean_injection_extension_adjoint_projection (h:euclidean_orthogonal_group R d) x:
  q (euclidean_rectangular_adjoint (injection_extension hCancel (orthogonal_element_map h)) x)=
    euclidean_rectangular_adjoint (orthogonal_element_map h) (q x).
Proof. by rewrite euclidean_injection_extension_adjoint injection_extension_projection. Qed.
End Inverse.
