(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import RelativeExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: the constructed relative exterior algebra is a
    W-module by multiplication by its coefficient inclusion. *)
Section RelativeModule.
Variable K : fieldType.
Variable W : algebra K.
Variable M : lmodType K.
Variable rho : W -> M -> M.
Local Notation R := (relative_exterior_algebra rho).
Local Notation c := (relative_coefficient rho).
Local Notation action := (@relative_action K W M rho).
(** Source for [relative_action_bilinear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_action_bilinear : bilinear action.
Proof. exact (bilinear_pre c (linear_id R) (alg_bilinear R)). Qed.
(** Source for [relative_action_unit]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_action_unit x : action (alg_one W) x = x.
Proof. by rewrite /relative_action algebra_map_one alg_unitl. Qed.
(** Source for [relative_action_assoc]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_action_assoc w z x : action w (action z x) = action (alg_mul W w z) x.
Proof. by rewrite /relative_action algebra_map_mul alg_assoc. Qed.
(** Source for [relative_action_scalar]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_action_scalar (a : K) x : action (a *: alg_one W) x = a *: x.
Proof. by rewrite /relative_action linearZ algebra_map_one (bilZl (alg_bilinear R)) alg_unitl. Qed.
(** Source for [relative_action_product]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_action_product w x y : action w (alg_mul R x y) = alg_mul R (action w x) y.
Proof. exact: alg_assoc. Qed.
End RelativeModule.
