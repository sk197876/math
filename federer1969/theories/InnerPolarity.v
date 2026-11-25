(** Federer (1969), 1.7.1, pp. 27-28: the polarity of an inner product. Its
    injectivity follows from definiteness, without any finite-dimensional
    hypothesis. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws BilinearPolarity
  AlternatingCoordinates Bilinear.
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
Local Notation F := (A_m V R^o 1).

(** Source for [inner_polarity]: Federer 1.7.1, pp. 27-28,
    the linear map into one-forms associated with the inner product. *)
Definition inner_polarity : {linear V -> F} :=
  GRing.Linear.clone _ _ _ _ (bilinear_polarity (inner_bilinear hB)) _.

(** Source for [inner_polarityE]: Federer 1.7.1, p. 27,
    the connecting equation for the inner-product polarity. *)
Lemma inner_polarityE x y : inner_polarity y [tuple x] = B x y.
Proof. exact: bilinear_polarityE. Qed.

(** Source for [inner_polarityP]: Federer 1.7.1, pp. 27-28,
    symmetry makes the associated map a polarity. *)
Lemma inner_polarityP : is_polarity inner_polarity.
Proof. move=> x y; by rewrite !inner_polarityE (inner_symmetric hB). Qed.

(** Source for [inner_polarity_injective]: Federer 1.7.1, pp. 27-28,
    supporting nondegeneracy of the inner-product polarity. *)
Theorem inner_polarity_injective : injective inner_polarity.
Proof.
move=> x y h.
have hz : x-y = 0.
  apply: (inner_right_separates hB) => z.
  by rewrite (bilBr (inner_bilinear hB)) -!inner_polarityE h subrr.
by apply/eqP; rewrite -subr_eq0 hz eqxx.
Qed.
End Polarity.
