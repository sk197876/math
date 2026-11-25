(** Federer (1969), 3.4.5, pp. 319–321:
    finite unions of actual set representatives
    preserve germ containment. This supplies the
    zero-dimensional endpoint of 3.4.10, p. 337. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import SetGermUP SetGermOrder SetGermBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_set_germ_union_monotone]: the
    finite union order law of 3.4.5,
    pp. 319–321, on actual representatives.
    Intersect the finitely many existing containment
    neighbourhoods; no new representative is selected. *)
Theorem finite_set_germ_union_monotone (X:topologicalType) (a:X) (J:finType)
    (S K:J->set X):
  (forall j,set_germ_subset (@set_germ X a (S j)) (@set_germ X a (K j))) ->
  set_germ_subset (@set_germ X a (\bigcup_j S j)) (@set_germ X a (\bigcup_j K j)).
Proof.
move=>hContained.
have hEach j:exists U:set X,open U /\U a /\forall x,S j x ->U x ->K j x.
  exact:(@set_germ_subset_original X a (S j) (K j)).1 (hContained j).
have [U hU]:=choice hEach.
pose C:set X:=\bigcup_j (~` U j).
have hC:closed C.
  apply:(closed_bigcup (@finite_finset J setT))=>j _.
  exact:open_closedC (hU j).1.
apply/set_germ_subset_original;exists (~` C);split;first exact:closed_openC hC.
split;first by move=>[j _ hNot];exact:hNot (hU j).2.1.
move=>x [j _ hxS] hxNot;exists j;first exact:Logic.I.
apply:((hU j).2.2 x hxS).
apply:contrapT=>hxBad;apply:hxNot;by exists j.
Qed.

(** Source for [finite_set_germ_empty_union]: finitely
    many empty germs have empty union,
    3.4.5, pp. 319–321, including an
    empty index family. Used at dimension
    zero in 3.4.10, p. 337. *)
Theorem finite_set_germ_empty_union (X:topologicalType) (a:X) (J:finType)
    (S:J->set X):
  (forall j,@set_germ X a (S j)=@set_germ X a set0) ->
  @set_germ X a (\bigcup_j S j)=@set_germ X a set0.
Proof.
move=>hEmpty.
have hEach j:set_germ_subset (@set_germ X a (S j)) (@set_germ X a set0).
  rewrite hEmpty;exact:set_germ_subset_reflexive.
have hSub:=@finite_set_germ_union_monotone X a J S (fun _=>set0) hEach.
have hUnion:(\bigcup_(_ :J) set0)=(@set0 X).
  apply/seteqP;split;[by move=>x [j _ []]|by move=>x].
rewrite hUnion in hSub;exact:set_germ_subset_empty hSub.
Qed.
