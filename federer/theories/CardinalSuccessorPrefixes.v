(** Federer (1969), 2.1.6(2), p. 59: each proper initial segment of a
    successor cardinal embeds in its predecessor. We derive the required
    representation from the abstract successor predicate and a well
    ordering, without an ordinal construction. Kelley, General Topology,
    Appendix, Definition 87/Theorem 88, p. 263, and cardinal comparison pp.
    275-276 (2017 reprint of 1955), supply the background. Our statement
    instead starts from an arbitrary well ordering and selects an
    equipollent subset using the successor hypothesis. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP WellOrderLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [cardinal_successor_small_prefixes]: Federer 2.1.6(2), p. 59,
    justification of the embeddings f_x. Starting with any well ordering of
    B, take its first initial segment too large to inject into A, or all of
    B if there is no such segment. This representative has cardinality B and
    every proper initial segment has cardinality at most A. This replaces
    the book's implicit use of initial ordinal representatives. it states
    the small-prefix well-ordering property for arbitrary cardinals, not
    this particular successor-subset lemma. *)
Theorem cardinal_successor_small_prefixes (I J : choiceType)
    (A : set I) (B : set J) (r : rel J) :
  is_cardinal_successor A B -> well_order r ->
  exists C, C `<=` B /\ B #<= C /\
    forall x, C x -> well_order_prefix C r x #<= A.
Proof.
move=> [_ [_ hs]] hw.
pose E := [set x | B x /\ ~ (well_order_prefix B r x #<= A)].
case: (pselect (exists x, E x))=> [hne|hempty].
- have [b [[hb hbad] hmin]] := well_order_set_minimum hw hne.
  pose C := well_order_prefix B r b.
  have hCB : C `<=` B by move=> x [hx _].
  exists C; split=> //; split.
  + exact: hs J C (subset_card_le hCB) hbad.
  + move=> x hx.
    have hsmall : well_order_prefix B r x #<= A.
      apply: contrapT=> hn.
      have he : E x by split; [exact: hCB x hx|exact hn].
      have hr := hmin x he.
      have hxb : x = b.
        apply: (well_order_antisymmetric_law hw); apply/andP; split=> //; exact: hx.2.1.
      exact: hx.2.2 hxb.
    apply: card_le_trans _ hsmall; apply: subset_card_le=> y [hy hrel].
    split=> //; exact: hCB.
- exists B; split; first by move=> x hx.
  split; first exact: card_lexx.
  move=> x hx; apply: contrapT=> hn; apply: hempty; exists x; by split.
Qed.
