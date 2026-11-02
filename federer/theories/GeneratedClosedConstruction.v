(** Federer (1969), 2.2.1, p. 60: existence of the two smallest closure
    families. This private intersection witness proves the abstract
    specification for either union convention. Source context and parameter
    convention: CountablyClosedFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [generated_closed_family_exists]: Federer
    2.2.1, p. 60, existence of the smallest family satisfying
    (2),(3), or (2)',(3), and containing S. Intersection preserves
    the selected closure laws. The bound by X includes the correct
    powerset restriction for empty classes of candidate families. *)
Lemma generated_closed_family_exists (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) :
  (forall A, S A -> A `<=` X) -> exists F, is_generated_closed_family d X S F.
Proof.
move=> hS.
pose Omega := [set F | is_countably_closed_family d X F /\ S `<=` F].
pose F := [set A | A `<=` X /\ forall G, Omega G -> G A].
have hF : is_countably_closed_family d X F.
  constructor.
  - split; first by move=> x [].
    move=> G [hG _]; exact: countably_closed_family_empty hG.
  - by move=> A [hA _].
  - move=> U hU hc hd; split.
    + move=> x [A hA hx]; exact: (hU A hA).1 x hx.
    + move=> G [hG hSG]; apply: (@countably_closed_family_union d I X G hG U)=> //.
      move=> A hA; apply: (hU A hA).2; by split.
  - move=> U hU hc hn; split.
    + have [A hA] := hn; move=> x hx; exact: (hU A hA).1 x (hx A hA).
    + move=> G [hG hSG]; apply: (@countably_closed_family_intersection d I X G hG U)=> //.
      move=> A hA; apply: (hU A hA).2; by split.
exists F; constructor=> //.
- move=> A hA; split; first exact: hS.
  move=> G [_ hs]; exact: hs.
- by move=> G hG hs A [_ ha]; apply: ha; split.
Qed.
