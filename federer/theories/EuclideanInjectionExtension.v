(** Federer (1969), 3.3.4, pp. 289–290:
    the actual orthogonal group on an active
    subspace embeds into the ambient orthogonal
    group by fixing its orthogonal complement.
    The underlying extension is already opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanInjectionRetraction
  InjectionExtensionUP InjectionExtension InjectionExtensionOrthogonal
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Extension.
Variable R:realType.
Variables d n:nat.
Variable w:Hom (R_n R d) (R_n R n).
Hypothesis hW:is_orthogonal_map (@euclidean_inner_product R d)
  (@euclidean_inner_product R n) (hom_as_linear w).
Local Notation q:=(euclidean_rectangular_adjoint w).
Local Notation hCancel:=(euclidean_orthogonal_injection_adjoint_cancel hW).

(** Source for [euclidean_injection_extension_orthogonality]:
    orthogonality of the actual active-space
    extension in Federer 3.3.4, pp. 289–290.
    The projection is the actual adjoint,
    whose cancellation and pairing laws have
    already been proved for the original inclusion. *)
Lemma euclidean_injection_extension_orthogonality (h:euclidean_orthogonal_group R d):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n)
    (hom_as_linear (injection_extension hCancel (orthogonal_element_map h))).
Proof.
exact:(@injection_extension_orthogonal R (R_n R d) (R_n R n)
  (@euclidean_inner_product R d) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R d) (@euclidean_inner_productP R n)
  w q (orthogonal_element_map h) (injection_extension hCancel (orthogonal_element_map h))
  hCancel (euclidean_rectangular_adjoint_pairing w)
  (orthogonal_element_orthogonal h) (injection_extension_specification hCancel (orthogonal_element_map h))).
Qed.

(** Source for [euclidean_injection_orthogonal_extension]:
    the member of O(n) acting by the
    original h on the actual active space
    and fixing its orthogonal complement,
    Federer 3.3.4, pp. 289–290. *)
Definition euclidean_injection_orthogonal_extension (h:euclidean_orthogonal_group R d):
    euclidean_orthogonal_group R n:=
  orthogonal_element_of (@euclidean_inner_productP R n) (@coordinate_basisP R n)
    (euclidean_injection_extension_orthogonality h).

(** Source for [euclidean_injection_orthogonal_extensionE]:
    the actual group member has precisely
    the existing opaque extension as its
    linear action, supporting Federer 3.3.4,
    pp. 289–290. *)
Lemma euclidean_injection_orthogonal_extensionE (h:euclidean_orthogonal_group R d) x:
  orthogonal_element_map (euclidean_injection_orthogonal_extension h) x=
    injection_extension hCancel (orthogonal_element_map h) x.
Proof. exact:orthogonal_element_ofE. Qed.

(** Source for [euclidean_injection_orthogonal_extension_active]:
    the actual extension acts on w(u)
    as w(h(u)), Federer 3.3.4, p. 290. *)
Lemma euclidean_injection_orthogonal_extension_active (h:euclidean_orthogonal_group R d) u:
  orthogonal_element_map (euclidean_injection_orthogonal_extension h) (w u)=
    w (orthogonal_element_map h u).
Proof.
rewrite euclidean_injection_orthogonal_extensionE.
exact:(injection_extension_specification hCancel (orthogonal_element_map h)).1 u.
Qed.

(** Source for [euclidean_injection_orthogonal_extension_fixed]:
    the actual extension fixes each original
    vector orthogonal to the active space,
    Federer 3.3.4, pp. 289–290. *)
Lemma euclidean_injection_orthogonal_extension_fixed (h:euclidean_orthogonal_group R d) x:
  q x=0 ->orthogonal_element_map (euclidean_injection_orthogonal_extension h) x=x.
Proof.
rewrite euclidean_injection_orthogonal_extensionE.
exact:(injection_extension_specification hCancel (orthogonal_element_map h)).2 x.
Qed.

(** Source for [euclidean_injection_orthogonal_extension_projection]:
    the actual projected extended vector
    equals h(q(x)), supporting the active
    coordinate calculation in Federer 3.3.4,
    pp. 290–291. *)
Lemma euclidean_injection_orthogonal_extension_projection (h:euclidean_orthogonal_group R d) x:
  q (orthogonal_element_map (euclidean_injection_orthogonal_extension h) x)=
    orthogonal_element_map h (q x).
Proof. by rewrite euclidean_injection_orthogonal_extensionE injection_extension_projection. Qed.
End Extension.
