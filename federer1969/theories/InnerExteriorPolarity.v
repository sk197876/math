(** Federer (1969), 1.7.5, pp. 31 and 33: beta_m is obtained from gamma_m by
    the canonical identification of m-forms with one-forms on m-vectors. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior InnerExteriorPositivity
  ExteriorGrading AlternatingCoordinates AlternatingIsomorphism
  OneFormIdentification OneFormLinear Hom AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Polarity.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.

(** Source for [exterior_polarity]: Federer 1.7.5,
    pp. 31-32, beta_m is the polarity of the induced inner
    product on m-vectors. Its defining diagram is verified below. *)
Definition exterior_polarity := inner_polarity (@exterior_inner_productP R h2 V B hB m).

(** Source for [exterior_polarity_identification]: Federer
    1.7.5, pp. 31 and 33, the canonical isomorphism from
    m-forms to one-forms on m-vectors takes gamma_m to beta_m. *)
Theorem exterior_polarity_identification (x : exterior_power V m) :
  exterior_polarity x = one_form (form_to_hom (inner_exterior_form h2 hB x)).
Proof.
apply: one_hom_injective; rewrite one_formK; apply: hom_ext => y.
rewrite one_homE /exterior_polarity.
rewrite (@inner_polarityE R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m)
  (@exterior_inner_productP R h2 V B hB m) y x).
by rewrite /exterior_inner_form /pairing.
Qed.

(** Source for [inner_exterior_form_injective]: Federer
    1.7.5, p. 33, injectivity of gamma_m. This part of the
    isomorphism assertion holds without finite dimension. *)
Theorem inner_exterior_form_injective : injective (@inner_exterior_form R h2 V B hB m).
Proof.
move=> x y h; apply: (@inner_polarity_injective R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m)
  (@exterior_inner_productP R h2 V B hB m) x y).
change (exterior_polarity x = exterior_polarity y).
by rewrite !exterior_polarity_identification h.
Qed.
End Polarity.
