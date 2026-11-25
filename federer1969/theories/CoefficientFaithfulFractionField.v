(** Federer (1969), 3.4.8(10), p. 330:
    when the original coefficient map is
    faithful, its original generated subfield
    is its fraction field. Apply the
    already proved coefficient-image fraction theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeSubringRealisationUP FractionFieldUP CoefficientFractionFieldUP
  CoefficientImageFractionField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [faithful_coefficient_fraction_field]: the
    original M is the fraction field
    of the original faithful Q_m image,
    as used for minimal polynomial coefficients
    in 3.4.8(10), p. 330. No fraction
    representation is constructed again. *)
Theorem faithful_coefficient_fraction_field (A:comNzRingType) (L M:fieldType)
  (original:{rmorphism A->L}) (eta:{rmorphism A->M}) (phi:{rmorphism M->L}):
  is_coefficient_fraction_field original eta phi ->injective original ->is_commutative_fraction_field eta.
Proof.
move=>hCoefficient hOriginal.
have hEta:injective eta.
  move=>a b hEqual;apply:hOriginal.
  by rewrite -(coefficient_fraction_scalar_triangle hCoefficient a)
    -(coefficient_fraction_scalar_triangle hCoefficient b) hEqual.
have hImage:is_commutative_subring_realisation (fun y:M=>exists a:A,y = eta a) eta.
  constructor;first exact:hEta.
  move=>y;split=>[[a hA]|[a hA]];exists a;exact:esym hA.
exact:(@coefficient_image_fraction_field A A L M original eta phi eta hCoefficient hImage).
Qed.
