(** Federer (1969), 2.10.28(1), proof p. 192: supporting finite sums of the
    two optional boundary losses. An absent boundary member contributes
    zero; an actual member contributes exactly once. This is finite-sum
    infrastructure, not an additional claim in the book. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [finite_optional_real_sum]: supporting
    single boundary contribution in the finite
    sum in 2.10.28(1), p. 192.
    Empty families and absent optional indices
    are included. *)
Lemma finite_optional_real_sum (R : realType) (I : choiceType)
    (F : {fset I}) (V : option I) (v : I -> R) :
  (forall i, V=Some i -> i \in F) ->
  \sum_(i <- F) (if V==Some i then v i else 0)=
    match V with Some i=>v i | None=>0 end.
Proof.
case: V=> [j|] hmem; last by apply: big1=> i _.
have hj : j \in F := hmem j (erefl _).
rewrite (big_fsetD1 _ hj) /= eqxx.
have hzero : (\sum_(i <- (F `\ j)%fset) (if Some j==Some i then v i else 0))=0.
  rewrite big_seq; apply: big1=> i hi.
  have hij : i!=j by move: hi; rewrite !inE=> /andP [].
  case: ifP=> // /eqP he.
  have heji : j = i by injection he.
  by rewrite heji eqxx in hij.
by rewrite hzero addr0.
Qed.
