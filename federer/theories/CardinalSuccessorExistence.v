(** Federer (1969), 2.5.11, p. 102: "For j in {1,2} let Y_j be a set with
    cardinal number aleph_j". The example presupposes such sets; their
    existence is a theorem of the set theory underlying the book (2.1.6, pp.
    58–59, cites Kelley's Appendix). Here aleph_1 is the successor of
    aleph_0 and aleph_2 the successor of aleph_1, in the sense of
    [is_cardinal_successor] (CardinalSuccessorUP.v). Well order the subsets
    of a representative of the given cardinal; by Cantor's theorem (Kelley,
    General Topology, Appendix, Theorem 161, p. 276, Dover 2017 reprint of
    1955) the whole power set is too large, so there is a least initial
    segment too large, or the whole power set when no initial segment is too
    large. Its proper initial segments are small, and the comparison of
    SmallPrefixInjectionSealed.v shows that it is a successor of the given
    cardinal, provided every set not bounded by the given cardinal bounds
    it. This holds for aleph_0 (an uncountable set is infinite) and for
    every successor of aleph_0. Kelley, Appendix, Theorems 150 and 157, p.
    275, give the well ordering of cardinals. *)
From mathcomp Require Import all_boot boolp classical_sets functions cardinality wochoice.
From Federer Require Import CardinalSuccessorUP CardinalInjection CardinalSuccessorPrefixes
  WellOrderLaws SmallPrefixInjectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [cantor_power_not_le]: Cantor's theorem, Kelley,
    Appendix, Theorem 161, p. 276, in the form needed for the sets
    Y_j of Federer 2.5.11, p. 102: the set of all subsets of I does
    not inject into I. *)
Lemma cantor_power_not_le (I : choiceType) : ~ (@setT (set I) #<= @setT I).
Proof.
move=> hle.
case: (pselect (exists d : I, True))=> [[d _]|hn].
- have [g [_ hg]] := cardinal_injection_with_default d hle.
  pose S := [set x : I | exists A : set I, g A = x /\ ~ A x].
  case: (pselect (S (g S)))=> hS.
  + have [A [hA hnA]] := hS.
    have he : A = S := hg A S (in_setT A) (in_setT S) hA.
    by apply: hnA; rewrite he.
  + by apply: (hS); exists S; split.
- have h0 : @setT I = set0.
    by apply/seteqP; split=> x // _; apply: hn; exists x.
  rewrite h0 in hle; move/card_le0P: hle=> he.
  have hT : (@setT (set I)) (@set0 I) by [].
  by rewrite he in hT.
Qed.

(** Source for [least_large_prefix]: supporting selection for the
    sets Y_j of Federer 2.5.11, p. 102. If the whole well ordered
    set is too large for A, the least initial segment which is too
    large (or the whole set, when there is none) is too large for A
    and all its proper initial segments are bounded by A. *)
Lemma least_large_prefix (I T : choiceType) (A : set I) (r : rel T) :
  well_order r -> ~ (@setT T #<= A) ->
  exists C : set T, ~ (C #<= A) /\ forall x, C x -> well_order_prefix C r x #<= A.
Proof.
move=> hw hT.
pose E := [set x | ~ (well_order_prefix setT r x #<= A)].
case: (pselect (exists x, E x))=> [hne|hempty].
- have [b [hbad hmin]] := well_order_set_minimum hw hne.
  exists (well_order_prefix setT r b); split; first exact: hbad.
  move=> x hx.
  have hsmall : well_order_prefix setT r x #<= A.
    apply: contrapT=> hn.
    have hrb := hmin x hn.
    have hxb : x = b.
      by apply: (well_order_antisymmetric_law hw); apply/andP; split=> //; exact: hx.2.1.
    exact: hx.2.2 hxb.
  apply: card_le_trans _ hsmall; apply: subset_card_le=> y [hy [hyx hyne]]; split=> //.
- exists setT; split; first exact: hT.
  move=> x _; apply: contrapT=> hn; apply: hempty; by exists x.
Qed.

(** Source for [cardinal_successor_exists]: existence of a successor
    cardinal, presupposed for the sets Y_j of Federer 2.5.11, p. 102;
    Kelley, Appendix, Theorems 150 and 161, pp. 275–276. The
    hypothesis says that every set whose cardinal is not at most that
    of A has cardinal at least that of A. *)
Theorem cardinal_successor_exists (I : choiceType) (A : set I) :
  (forall (K : choiceType) (B : set K), ~ (B #<= A) -> A #<= B) ->
  exists J : choiceType, is_cardinal_successor A (@setT J).
Proof.
move=> hcmp.
have [r hw] := well_ordering_principle (set I).
have hT : ~ (@setT (set I) #<= A).
  by move=> h; apply: (@cantor_power_not_le I); exact: card_le_trans h (card_leT A).
have [C [hC hp]] := least_large_prefix hw hT.
exists [the choiceType of set_type C].
have := card_setT_sym C; move/card_eqPle=> [hCJ _].
have := card_setT C; move/card_eqPle=> [hJC _].
have hJ : ~ (@setT (set_type C) #<= A) by move=> h; exact: hC (card_le_trans hCJ h).
split; first exact: hcmp _ _ hJ.
split; first exact: hJ.
move=> K D _ hD; apply: card_le_trans hJC _.
exact: (SmallPrefixInjection.injects hw hp hD).
Qed.

(** Source for [countable_lower_comparable]: a set which is not
    countable has cardinal at least aleph_0, supporting the
    existence of Y_1 in Federer 2.5.11, p. 102. *)
Lemma countable_lower_comparable (K : choiceType) (B : set K) :
  ~ (B #<= @setT nat) -> @setT nat #<= B.
Proof. move=> hB; apply/infiniteP=> hf; apply: hB; exact: finite_set_countable hf. Qed.

(** Source for [aleph_one_exists]: existence of a set Y_1 with
    cardinal number aleph_1, presupposed in Federer 2.5.11, p. 102. *)
Theorem aleph_one_exists : exists J1 : choiceType, is_cardinal_successor (@setT nat) (@setT J1).
Proof. apply: cardinal_successor_exists=> K B; exact: countable_lower_comparable. Qed.

(** Source for [successor_lower_comparable]: a set whose cardinal is
    not at most aleph_1 has cardinal at least aleph_1, by the small
    initial segments of 2.1.6(2), p. 59 (CardinalSuccessorPrefixes.v);
    supporting the existence of Y_2 in Federer 2.5.11, p. 102. *)
Lemma successor_lower_comparable (J1 : choiceType) :
  is_cardinal_successor (@setT nat) (@setT J1) ->
  forall (K : choiceType) (B : set K), ~ (B #<= @setT J1) -> @setT J1 #<= B.
Proof.
move=> h1 K B hB.
have [r hw] := well_ordering_principle J1.
have [C [_ [hBC hp]]] := cardinal_successor_small_prefixes h1 hw.
apply: card_le_trans hBC _.
apply: (SmallPrefixInjection.injects hw hp).
by move=> hc; apply: hB; exact: card_le_trans hc h1.1.
Qed.

(** Source for [aleph_two_exists]: existence of a set Y_2 with
    cardinal number aleph_2, presupposed in Federer 2.5.11, p. 102,
    for every set Y_1 with cardinal number aleph_1. *)
Theorem aleph_two_exists (J1 : choiceType) :
  is_cardinal_successor (@setT nat) (@setT J1) ->
  exists J2 : choiceType, is_cardinal_successor (@setT J1) (@setT J2).
Proof. move=> h1; apply: cardinal_successor_exists; exact: successor_lower_comparable h1. Qed.

(** Source for [aleph_one_two_exist]: the sets Y_1 and Y_2 with
    cardinal numbers aleph_1 and aleph_2 presupposed in Federer
    2.5.11, p. 102, exist. *)
Theorem aleph_one_two_exist : exists J1 J2 : choiceType,
  is_cardinal_successor (@setT nat) (@setT J1) /\ is_cardinal_successor (@setT J1) (@setT J2).
Proof.
have [J1 h1] := aleph_one_exists; have [J2 h2] := aleph_two_exists h1.
by exists J1, J2.
Qed.
