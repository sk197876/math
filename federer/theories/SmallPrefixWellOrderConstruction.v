(** Private set-theoretic witness for Federer (1969), 2.2.4, p. 62 Start
    with an arbitrary well ordering and cut it at the first initial segment
    of full cardinality, if such a segment exists. The resulting carrier is
    equipollent to the original set and every proper prefix is strictly
    smaller. This is the subset version of taking the initial ordinal,
    retaining the proof's cardinal content. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP WellOrderLaws SmallPrefixWellOrderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [small_prefix_well_order_exists]: existence for the
    specification used in Federer 2.2.4, p. 62. Minimality of the first
    full-cardinality prefix prevents any earlier prefix from having full
    cardinality. The empty set is included. *)
Theorem small_prefix_well_order_exists (J : choiceType) (D : set J) :
  exists C r, is_small_prefix_well_order D C r.
Proof.
have [r hw] := well_ordering_principle J.
pose E := [set x | D x /\ D #<= well_order_prefix D r x].
case: (pselect (exists x, E x))=> [hne|hempty].
- have [b [[hb hfull] hmin]] := well_order_set_minimum hw hne.
  pose C := well_order_prefix D r b.
  have hCD : C `<=` D by move=> x [hx _].
  exists C, r; constructor; [exact hw|exact hCD|exact hfull|].
  move=> x hx hbad.
  have hsub : well_order_prefix C r x `<=` well_order_prefix D r x.
    move=> y [hy hrel]; split=> //; exact: hCD y hy.
  have he : E x by split; [exact: hCD x hx|exact: card_le_trans hbad (subset_card_le hsub)].
  have hbx := hmin x he.
  have hxb : x = b.
    apply: (well_order_antisymmetric_law hw); apply/andP; split=> //; exact: hx.2.1.
  exact: hx.2.2 hxb.
- exists D, r; constructor; [exact hw|by move=> x hx|exact: card_lexx|].
  move=> x hx hbad; apply: hempty; exists x; by split.
Qed.
