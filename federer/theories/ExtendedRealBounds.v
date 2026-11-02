(** Federer (1969), 2.1.1, p. 51: every extended-real set has a supremum and
    an infimum, including the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBoundsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_sup]: Federer 2.1.1, p. 51,
    third paragraph; supremum exposed only through its order laws. *)
Definition extended_real_sup (R : realType) (S : set (\bar R)) :=
  ExtendedRealBounds.value S.

(** Source for [extended_real_inf]: Federer 2.1.1, p. 51,
    third paragraph; infimum, defined by order duality. *)
Definition extended_real_inf (R : realType) (S : set (\bar R)) :=
  - extended_real_sup [set y | S (- y)].

(** Source for [extended_real_sup_upper]: Federer 2.1.1,
    p. 51, third paragraph; every member is below the supremum. *)
Lemma extended_real_sup_upper (R : realType) (S : set (\bar R)) x :
  S x -> x <= extended_real_sup S.
Proof. exact: (@extended_real_supremum_upper R S _ (ExtendedRealBounds.laws S) x). Qed.

(** Source for [extended_real_sup_least]: Federer 2.1.1,
    p. 51, third paragraph; the supremum is the least upper bound. *)
Lemma extended_real_sup_least (R : realType) (S : set (\bar R)) d :
  (forall x, S x -> x <= d) -> extended_real_sup S <= d.
Proof. exact: (@extended_real_supremum_least R S _ (ExtendedRealBounds.laws S) d). Qed.

(** Source for [extended_real_inf_lower]: Federer 2.1.1,
    p. 51, third paragraph; the infimum is a lower bound. *)
Lemma extended_real_inf_lower (R : realType) (S : set (\bar R)) x :
  S x -> extended_real_inf S <= x.
Proof.
move=> hx; rewrite /extended_real_inf leeNl.
apply: extended_real_sup_upper; by rewrite /= oppeK.
Qed.

(** Source for [extended_real_inf_greatest]: Federer 2.1.1,
    p. 51, third paragraph; the infimum is the greatest lower bound. *)
Lemma extended_real_inf_greatest (R : realType) (S : set (\bar R)) d :
  (forall x, S x -> d <= x) -> d <= extended_real_inf S.
Proof.
move=> hl; rewrite /extended_real_inf leeNr; apply: extended_real_sup_least.
move=> x hx; rewrite leeNr; exact: hl.
Qed.

(** Source for [extended_real_sup_empty]: Federer 2.1.1,
    p. 51, third paragraph; the empty supremum is negative infinity. *)
Lemma extended_real_sup_empty (R : realType) :
  extended_real_sup (@set0 (\bar R)) = -oo.
Proof.
apply/eqP; rewrite eq_le leNye andbT; apply: extended_real_sup_least.
by move=> x [].
Qed.

(** Source for [extended_real_inf_empty]: Federer 2.1.1,
    p. 51, third paragraph; the empty infimum is positive infinity. *)
Lemma extended_real_inf_empty (R : realType) :
  extended_real_inf (@set0 (\bar R)) = +oo.
Proof. by rewrite /extended_real_inf extended_real_sup_empty. Qed.

(** Source for [extended_real_inf_le_sup]: Federer 2.1.1, p. 51, third
    paragraph; infimum is at most supremum for a nonempty set. *)
Lemma extended_real_inf_le_sup (R : realType) (S : set (\bar R)) :
  S !=set0 -> extended_real_inf S <= extended_real_sup S.
Proof.
move=> [x hx]; exact: le_trans (extended_real_inf_lower hx) (extended_real_sup_upper hx).
Qed.
