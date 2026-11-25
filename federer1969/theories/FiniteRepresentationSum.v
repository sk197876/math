(** Federer (1969), 3.1.11, p. 222: supporting finite
    reindexing in the regrouping of the multinomial expansion by
    weighted degree. Every represented multiindex is counted once. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_representation_single_sum]: the unique
    occurrence of a multiindex contributes its value once in the
    sums of Federer 3.1.11, p. 222. *)
Lemma finite_representation_single_sum (I : finType) (T : eqType)
    (V : zmodType) (u : I->T) (P : pred I) (F : T->V) t :
  injective u -> (exists i, P i /\ u i=t) ->
  \sum_(i | P i) (if u i==t then F (u i) else 0)=F t.
Proof.
move=>hinj [i [hPi hit]].
rewrite (bigD1 i hPi) /= hit eqxx.
have hz : \sum_(j | P j && (j!=i)) (if u j==t then F (u j) else 0)=0.
  apply: big1=>j /andP [hPj hji].
  case h : (u j==t)=> //.
  have he : j = i := hinj j i (eq_trans (eqP h) (esym hit)).
  by move:hji; rewrite he eqxx.
by rewrite hz addr0.
Qed.

(** Source for [finite_representation_sum]: regrouping the
    multiindices in the Taylor composition calculation, Federer
    3.1.11, p. 222. Two injective finite presentations of the
    same restricted family give the same finite sum. *)
Lemma finite_representation_sum (I J : finType) (T : eqType)
    (V : zmodType) (u : I->T) (v : J->T)
    (P : pred I) (Q : pred J) (F : T->V) :
  injective u -> injective v ->
  (forall i, P i -> exists j, Q j /\ v j=u i) ->
  (forall j, Q j -> exists i, P i /\ u i=v j) ->
  \sum_(i | P i) F (u i)=\sum_(j | Q j) F (v j).
Proof.
move=>hu hv huv hvu.
transitivity (\sum_(i | P i) \sum_(j | Q j)
  (if v j==u i then F (v j) else 0)).
- apply: eq_bigr=>i hi; symmetry.
  exact (@finite_representation_single_sum J T V v Q F (u i) hv (huv i hi)).
rewrite exchange_big.
apply: eq_bigr=>j hj.
transitivity (\sum_(i | P i) (if u i==v j then F (u i) else 0)).
- apply: eq_bigr=>i _; rewrite eq_sym; case: eqP=> [->|//]; by [].
- exact (@finite_representation_single_sum I T V u P F (v j) hu (hvu j hj)).
Qed.
