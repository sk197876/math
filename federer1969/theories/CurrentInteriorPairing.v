(** Federer (1969), 4.1.7, pp. 355–356:
    the original right interior used in the
    current vector product. Its characteristic pairing
    is the earlier 1.5.1 law, p. 21,
    including scalar output degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom ExteriorGrading ExteriorAlgebra ExteriorHomogeneousProducts
  AlternatingForms AlternatingExtension AlternatingZero AlternatingIsomorphism AlternatingPairing AlternatingSum
  AlternatingUnit RightInterior ComassWedgeSymmetry CurrentVectorFormInterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_vector_form_interior_include]:
    the original test interior has precisely the
    right-interior characteristic action, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma current_vector_form_interior_include (K:fieldType) (V:lmodType K) k p
    (xi:exterior_power V k) (phi:A_m V K^o (k+p)) (x:exterior_space V):
  form_include (current_vector_form_interior xi phi) x=
    form_include phi (wedge x (component_val xi)).
Proof.
rewrite /current_vector_form_interior form_reindex_include.
change (form_homogeneous (right_interior (leq_addr p k) xi phi) x=
  form_homogeneous phi (wedge x (component_val xi))).
exact:right_interior_homogeneousE.
Qed.

(** Source for [current_zero_covector_unit_value]:
    the original zero-covector scalar is its
    evaluation at the exterior unit, supporting
    Federer 4.1.7, pp. 355–356, by
    1.4.2, p. 18. *)
Lemma current_zero_covector_unit_value (K:fieldType) (V:lmodType K) (phi:A_m V K^o 0):
  form_include phi (exterior_unit V)=zero_form_value phi.
Proof.
rewrite -{1}(zero_form_valueK phi).
change (coefficient_form V (zero_form_value phi) (exterior_unit V)=zero_form_value phi).
by rewrite coefficient_formE exterior_augmentation_unit scale1r.
Qed.

(** Source for [current_vector_interior_scalar_value]:
    equal-degree right interior is the original
    scalar pairing, supporting the coordinate current
    expansion in Federer 4.1.7, p. 356.
    Equal input degrees remain explicit. *)
Lemma current_vector_interior_scalar_value (K:fieldType) (V:lmodType K) k
    (xi:exterior_power V k) (phi:A_m V K^o (k+0)):
  zero_form_value (current_vector_form_interior xi phi)=form_include phi (component_val xi).
Proof.
rewrite -current_zero_covector_unit_value current_vector_form_interior_include.
by rewrite wedge_unitl.
Qed.
