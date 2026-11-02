(** Federer (1969), 2.2.1, pp. 59-60: intersection of Borel families,
    including the largest family of all subsets. We bound intersections by
    the powerset of X, so that the empty intersection is exactly that
    largest family. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_family_powerset]: Federer 2.2.1, p. 59, the family of
    all subsets of X is the largest Borel family *)
Lemma borel_family_powerset (I : choiceType) (X : set I) :
  is_borel_family X [set A | A `<=` X].
Proof.
constructor.
- by move=> x [].
- by move=> A hA.
- by move=> A hA x [hx _].
- move=> G hG _ x [A hA hx]; exact: hG A hA x hx.
- move=> G hG _ [A hA] x hx; exact: hG A hA x (hx A hA).
Qed.

(** Source for [borel_family_intersection]: Federer 2.2.1, pp. 59-60,
    arbitrary intersection of Borel families. This uses intersection within
    the powerset of X; hence the empty family yields the largest Borel
    family rather than sets outside X. *)
Lemma borel_family_intersection (I : choiceType) (X : set I)
    (Omega : set (set (set I))) :
  (forall F, Omega F -> is_borel_family X F) ->
  is_borel_family X [set A | A `<=` X /\ forall F, Omega F -> F A].
Proof.
move=> hO; constructor.
- split; first by move=> x [].
  move=> F hF; exact: borel_family_empty (hO F hF).
- by move=> A [hA _].
- move=> A [hA ha]; split; first by move=> x [hx _].
  move=> F hF; exact: (@borel_family_complement I X F (hO F hF) A (ha F hF)).
- move=> G hG hc; split.
  + move=> x [A hA hx]; exact: (hG A hA).1 x hx.
  + move=> F hF; apply: (borel_family_countable_union (hO F hF))=> //.
    move=> A hA; exact: (hG A hA).2 F hF.
- move=> G hG hc hn; split.
  + have [A hA] := hn; move=> x hx; exact: (hG A hA).1 x (hx A hA).
  + move=> F hF; apply: (borel_family_countable_intersection (hO F hF))=> //.
    move=> A hA; exact: (hG A hA).2 F hF.
Qed.
