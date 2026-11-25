(** Federer (1969), 4.1.8, p. 362: identify the
    original vector and exterior one-vector in the
    segment pairing. These are the existing 1.3.1,
    p. 13, and 1.4.1, p. 17, identifications. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom GradedComponents ExteriorAlgebra ExteriorGrading ExteriorPowers
  FiniteExteriorPowers AlternatingForms AlternatingPairing CovectorProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [exterior_first_single_tuple]: the original
    one-vector is its single-factor exterior product,
    supporting Federer 4.1.8, p. 362, by 1.3.1, p. 13. *)
Lemma exterior_first_single_tuple (K:fieldType) (V:lmodType K) (w:V):
  e_lambda (@idfun V) [tuple w]=exterior_first_inclusion V w.
Proof.
apply:val_inj.
change (component_val (e_lambda (@idfun V) [tuple w])=
  component_val (exterior_first_inclusion V w)).
rewrite e_lambdaE map_id.
change (exterior_word [::w]=exterior_degree 1 (exterior_generator w)).
by rewrite exterior_generator_homogeneous exterior_word_cons exterior_word_nil wedge_unitr.
Qed.

(** Source for [exterior_first_pairing_tuple]: the original
    vector/one-form pairing is the one-form's single
    argument value, supporting Federer 4.1.8, p. 362. *)
Lemma exterior_first_pairing_tuple (K:fieldType) (V W:lmodType K)
    (w:V) (phi:A_m V W 1):pairing (exterior_first_inclusion V w) phi=phi [tuple w].
Proof.
rewrite -exterior_first_single_tuple pairing_e_lambda.
have hTuple:[tuple of map (@idfun V) [tuple w]]=[tuple w].
  by apply:eq_from_tnth=>i;rewrite tnth_map.
by rewrite hTuple.
Qed.
