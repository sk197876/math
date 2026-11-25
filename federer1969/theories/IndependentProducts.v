(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SimpleWordIndependence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: the exterior product of an independent family is
    nonzero, by pairing it with the product of a dual family. *)
Section Product.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Hypothesis he : finite_independent e.
(** Source for [independent_product_nonzero]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem independent_product_nonzero : e_lambda e (ord_tuple m) != 0.
Proof.
pose omega i := one_form (independent_dual he i).
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite /omega one_formE independent_dualE.
have h := @pairing_e_omega K h2 V m m omega e hd (Lambda_top m) (Lambda_top m).
rewrite eqxx in h.
apply/eqP=> hz.
change (pairing (e_lambda e (ord_tuple m)) (omega_lambda h2 omega (Lambda_top m)) = 1) in h.
rewrite hz /pairing linear0 in h.
by move: (oner_neq0 K); rewrite -h eqxx.
Qed.
(** Source for [independent_word_nonzero]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem independent_word_nonzero : exterior_word [seq e i | i <- enum 'I_m] != 0.
Proof.
apply/eqP=> hz; apply: (elimT negP independent_product_nonzero); apply/eqP; apply: val_inj.
change (component_val (e_lambda e (ord_tuple m)) = component_val (0 : exterior_power V m)).
by rewrite e_lambdaE linear0.
Qed.
End Product.
