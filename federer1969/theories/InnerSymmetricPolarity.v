(** Federer (1969), 1.10.5, p. 47, first paragraph: the inner-product
    polarity takes values in symmetric one-forms. This is the existing
    polarity of 1.7.1 under the proved one-form and symmetric-first-power
    identifications. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Hom HomogeneousHom InnerProductUP InnerPolarity
  OneFormIdentification OneFormLinear SymmetricAlgebra SymmetricGrading
  SymmetricLowPowers SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Polarity.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_symmetric_polarity]: Federer 1.10.5,
    p. 47, the given polarity, expressed as a symmetric
    one-form. No basis or finite-dimensional hypothesis is used. *)
Definition inner_symmetric_polarity (y : V) : S_m V R^o 1 :=
  hom_to_sform (hom_comp (one_hom (inner_polarity hB y))
    (hom_of_linear (symmetric_first_inverse V))).

(** Source for [inner_symmetric_polarity_linear]: Federer
    1.10.5, p. 47, supporting linearity of the
    generator map to be extended to the symmetric algebra. *)
Lemma inner_symmetric_polarity_linear : linear inner_symmetric_polarity.
Proof.
move=> a y z; rewrite /inner_symmetric_polarity !linearP hom_precompose_linear.
exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R V (S_m V R^o 1) *:%R
  inner_symmetric_polarity inner_symmetric_polarity_linear.

(** Source for [inner_symmetric_polarityE]: Federer 1.10.5,
    p. 47, the polarity pairs x with y to give
    their original inner product. *)
Lemma inner_symmetric_polarityE x y :
  symmetric_pairing (symmetric_first_inclusion V x) (inner_symmetric_polarity y) = B x y.
Proof.
change (sform_to_hom (inner_symmetric_polarity y) (symmetric_first_inclusion V x) = B x y).
rewrite /inner_symmetric_polarity hom_to_sformK hom_compE hom_of_linearE
  symmetric_first_inclusionK.
change (one_hom (inner_polarity hB y) x = B x y).
rewrite one_homE.
exact: inner_polarityE.
Qed.
End Polarity.
