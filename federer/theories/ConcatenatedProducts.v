(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace ConcatenatedFamilies
  SimpleProducts SimpleElementary SimpleWordIndependence IndependentProducts
  IndependentConcatenation FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, third corollary: the product of two simple products
    is the product of their concatenated families. Nonvanishing is
    exactly the independence of this combined family. *)
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m n : nat.
Variables (e : 'I_m -> V) (f : 'I_n -> V).
Local Notation xi := (e_lambda e (ord_tuple m)).
Local Notation eta := (e_lambda f (ord_tuple n)).
Local Notation zeta := (e_lambda (concatenate_family e f) (ord_tuple (m+n))).
(** Source for [concatenated_product]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenated_product : exterior_product xi eta = zeta.
Proof.
apply: val_inj.
change (component_val (exterior_product xi eta) = component_val zeta).
by rewrite exterior_productE !e_lambdaE concatenate_family_sequence exterior_word_cat.
Qed.
(** Source for [concatenated_product_independent]: Federer (1969), 1.6.1, p.
    24, third corollary. In words: The wedge of two nonzero simple vectors
    is nonzero exactly when its associated subspace is the direct sum of
    their associated subspaces. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma concatenated_product_independent : zeta != 0 -> finite_independent (concatenate_family e f).
Proof.
move=> hz; apply: nonzero_word_independent.
apply/eqP=> h; apply: (elimT negP hz); apply/eqP; apply: val_inj.
change (component_val zeta = component_val (0 : exterior_power V (m+n))).
by rewrite e_lambdaE linear0.
Qed.
(** Source for [concatenated_product_space]: Federer (1969), 1.6.1, p. 24,
    third corollary. In words: The wedge of two nonzero simple vectors is
    nonzero exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem concatenated_product_space : zeta != 0 -> forall v,
  FedererSimple.T zeta v <->
  exists x y, in_finite_span e x /\ in_finite_span f y /\ v=x+y.
Proof.
move=> hz v; rewrite (@product_associated_space K h2 V (m+n) (concatenate_family e f) hz v) concatenate_family_span; reflexivity.
Qed.
End Products.
