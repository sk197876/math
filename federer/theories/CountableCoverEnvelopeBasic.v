(** Federer (1969), 2.10.1, pp. 169–170: order consequences of the
    covering-infimum specification, used for the 2.3.8, p. 78,
    counterexample. Source context: CountableCoverEnvelopeUP.v. No
    construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport CountableCoverEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Laws.
Variables (R : realType) (X J : choiceType) (S : J -> set X).
Variables (cost : J -> \bar R) (nu : set X -> \bar R).
Hypothesis hn : is_countable_cover_envelope S cost nu.

(** Source for [countable_cover_envelope_nonnegative]: nonnegative
    covering costs give nonnegative infima, Federer 2.10.1, p. 170. *)
Lemma countable_cover_envelope_nonnegative A : 0 <= nu A.
Proof. apply: (countable_cover_envelope_greatest hn)=> G _ _; exact: nonnegative_sum_nonnegative. Qed.

(** Source for [countable_cover_envelope_empty]: the empty cover gives zero
    measure to the empty set in Federer 2.10.1, p. 170 *)
Lemma countable_cover_envelope_empty : nu set0 = 0.
Proof.
apply/eqP; rewrite eq_le countable_cover_envelope_nonnegative andbT.
have he : (@set0 X) `<=` \bigcup_(j in (@set0 J)) S j by move=> x [].
have h := countable_cover_envelope_lower hn (countable0 J) he.
by rewrite nonnegative_sum_empty in h.
Qed.

(** Source for [countable_cover_envelope_mono]: inclusion reduces
    the covering constraints in Federer 2.10.1, p. 170. *)
Lemma countable_cover_envelope_mono A B : A `<=` B -> nu A <= nu B.
Proof.
move=> hAB; apply: (countable_cover_envelope_greatest hn)=> G hc hB.
apply: (countable_cover_envelope_lower hn hc)=> x hx; exact: hB (hAB x hx).
Qed.

(** Source for [countable_cover_envelope_generator_bound]: the
    singleton cover bounds each generator's measure by its assigned
    cost, supporting Federer 2.10.1, p. 170. *)
Lemma countable_cover_envelope_generator_bound j : 0 <= cost j -> nu (S j) <= cost j.
Proof.
move=> hj; have hc : S j `<=` \bigcup_(k in [set j]) S k.
  move=> x hx; by exists j.
have h := countable_cover_envelope_lower hn (countable1 j) hc.
by rewrite nonnegative_sum_singleton in h.
Qed.

(** Source for [countable_cover_envelope_approximation]: Supporting Federer
    2.10.1, p. 170. *)
Lemma countable_cover_envelope_approximation A b : nu A < b ->
  exists G, countable G /\ A `<=` \bigcup_(j in G) S j /\ nonnegative_sum G cost < b.
Proof.
move=> hb; apply: contrapT=> hnG.
have hbn : b <= nu A.
  apply: (countable_cover_envelope_greatest hn)=> G hc hcov.
  rewrite leNgt; apply/negP=> hlt; apply: hnG; exists G; by split=> //; split.
by move: hb; rewrite ltNge hbn.
Qed.
End Laws.
