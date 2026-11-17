(** Elementary finite summation support for the expanded continuity
    argument of Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_uniform_chain_increment]: supporting the
    sum of the row-replacement errors in Federer 3.2.45,
    p. 279. A finite real chain with each increment at most c
    has total increment at most N c. The constant may have either
    sign, and the empty chain is retained. This is a helper, not
    a separately numbered assertion in the book. *)
Lemma finite_uniform_chain_increment (R : realType) (a : nat -> R) (c : R) N :
  (forall j, (j < N)%N -> a j.+1 <= a j+c) ->
  a N <= a 0+N%:R*c.
Proof.
elim: N=> [hStep|N hIH hStep].
- by rewrite mul0r addr0.
- have hPrevious := hIH (fun j hj => hStep j (ltn_trans hj (ltnSn N))).
  have hLast := hStep N (ltnSn N).
  have h := le_trans hLast (lerD hPrevious (lexx c)).
  have hEquality : a 0+N%:R*c+c = a 0+N.+1%:R*c.
    rewrite -[N.+1]addn1 natrD; ring.
  by rewrite hEquality in h.
Qed.
