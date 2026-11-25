(** Federer (1969), 4.1.6, p. 351: when
    the degrees agree, contraction is the original
    pairing. The degree-zero output is read through
    A^0(V,W)=W by evaluation at the exterior unit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Alternating InteriorMultiplication RightInterior
  PointwiseFieldSpaceSealed DifferentialFormFields DifferentialFormContractions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [field_pairing_interior_evaluation]: the
    original equal-degree notation <xi,phi>,
    Federer 4.1.6, p. 351, agrees with
    the actual preceding interior operation. *)
Lemma field_pairing_interior_evaluation (K:fieldType) (X:choiceType) (V W:lmodType K) m
    (xi:multivector_field_space K X V m) (phi:differential_form_space K X V W m) x:
  form_include (@differential_form_value K X V W (m-m)
    (field_right_interior (leqnn m) xi phi) x) (exterior_unit V)=
  @PointwiseFieldSpace.value K X W (field_form_pairing xi phi) x.
Proof.
rewrite field_right_interior_values field_form_pairing_values form_includeE
  -form_homogeneousE right_interior_homogeneousE wedge_unitl.
by rewrite /pairing form_to_homE form_homogeneousE.
Qed.
