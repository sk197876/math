(** A local counterexample cost for Federer (1969), 2.10.17(2), p. 179, when
    its density quotient retains the original partial arithmetic of 2.1.1,
    p. 51. Charge zero for sets with at most one point and one for all other
    sets. it is a local counterexample, not the irrational-interval example
    stated there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subsingleton_cover_cost]: local cost
    supporting the counterexample to 2.10.17(2),
    p. 179. All singleton covers are free, whereas
    every set containing two distinct points costs one. *)
Definition subsingleton_cover_cost (R : realType) (X : Type) (S : set X) : \bar R :=
  if pselect (forall x y, S x -> S y -> x=y) then 0 else 1.

(** Source for [subsingleton_cover_cost_nonnegative]:
    supporting nonnegative-cost hypothesis of 2.10.1,
    p. 170, for the local 2.10.17 counterexample. *)
Lemma subsingleton_cover_cost_nonnegative (R : realType) (X : Type) (S : set X) :
  0<=subsingleton_cover_cost R S.
Proof. by rewrite /subsingleton_cover_cost; case: pselect=> _ //; rewrite lee_fin ler01. Qed.

(** Source for [subsingleton_cover_cost_singleton]:
    supporting free singleton cover for the local
    counterexample to 2.10.17(2), p. 179. *)
Lemma subsingleton_cover_cost_singleton (R : realType) (X : Type) (a : X) :
  subsingleton_cover_cost R [set a]=0.
Proof.
rewrite /subsingleton_cover_cost; case: pselect=> h //.
exfalso; apply: h; by move=> x y -> ->.
Qed.

(** Source for [subsingleton_cover_cost_pair]: supporting
    positive-cost small sets for the local counterexample
    to 2.10.17(2), p. 179. Any two distinct points
    form a set of cost one. *)
Lemma subsingleton_cover_cost_pair (R : realType) (X : choiceType) (a b : X) :
  a!=b -> subsingleton_cover_cost R ([set a] `|` [set b])= 1.
Proof.
move=> hab; rewrite /subsingleton_cover_cost; case: pselect=> h //.
have he : a=b := h a b (or_introl (erefl a)) (or_intror (erefl b)).
exfalso; apply: (negP hab); apply/eqP; exact he.
Qed.

(** Source for [subsingleton_cover_cost_nonzero]: supporting
    exact value of every defined denominator in the
    local partial-quotient counterexample to 2.10.17(2),
    p. 179. Every nonzero cost is exactly one. *)
Lemma subsingleton_cover_cost_nonzero (R : realType) (X : Type) (S : set X) :
  subsingleton_cover_cost R S!=0 -> subsingleton_cover_cost R S= 1.
Proof. by rewrite /subsingleton_cover_cost; case: pselect=> h //; rewrite eqxx. Qed.
