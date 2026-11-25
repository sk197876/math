(** Federer (1969), 2.5.8, p. 100: the countable envelope g=sup_n |f_n|.
    Finite maxima supply increasing approximants to this envelope. These
    finite auxiliary expressions do not replace the abstract specification
    of the limiting function. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [increasing_absolute_maximum]: supporting finite maxima for
    the supremum in Federer 2.5.8, p. 100 *)
Fixpoint increasing_absolute_maximum (R : realType) (X : Type)
    (f : nat -> X -> R) (n : nat) (x : X) : R :=
  if n is m.+1 then Order.max (increasing_absolute_maximum f m x) `|f m.+1 x|
  else `|f 0%N x|.

(** Source for [increasing_absolute_maximum_nonnegative]: supporting
    positivity of the envelope in Federer 2.5.8, p. 100, corrected by
    erratum p. 2, line 9 *)
Lemma increasing_absolute_maximum_nonnegative (R : realType) (X : Type)
    (f : nat -> X -> R) n x : 0 <= increasing_absolute_maximum f n x.
Proof. case: n=> [|n]; first exact: normr_ge0. by rewrite /= le_max normr_ge0 orbT. Qed.

(** Source for [increasing_absolute_maximum_diagonal]: every sequence member
    is dominated by the supremum in Federer 2.5.8, p. 100 *)
Lemma increasing_absolute_maximum_diagonal (R : realType) (X : Type)
    (f : nat -> X -> R) n x : `|f n x| <= increasing_absolute_maximum f n x.
Proof. case: n=> [|n] //=; by rewrite le_max lexx orbT. Qed.

(** Source for [increasing_absolute_maximum_increases]: supporting
    approximation to the supremum in Federer 2.5.8, p. 100 *)
Lemma increasing_absolute_maximum_increases (R : realType) (X : Type)
    (f : nat -> X -> R) n m x :
  (n <= m)%N -> increasing_absolute_maximum f n x <= increasing_absolute_maximum f m x.
Proof.
elim: m=> [|m ih] in n *; first by rewrite leqn0=> /eqP ->.
case: (eqVneq n m.+1)=> [->|hne] hnm; first exact: lexx.
have hn : (n <= m)%N by rewrite -ltnS ltn_neqAle hne hnm.
apply: le_trans (ih n hn) _; by rewrite /= le_max lexx.
Qed.
