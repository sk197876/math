(** Federer (1969), 2.2.10, p. 67, first paragraph, with the correction in
    the working erratum p. 1, book p. 67 line 2: both family operations are
    unions. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_separated_countable_unions]: direct corrected
    countable-family assertion in Federer 2.2.10, p. 67: if every P in G and
    Q in H are Borel separated, then the union of G and the union of H are
    Borel separated. Erratum p. 1, book p. 67 line 2 Complements of
    countable unions also handle empty indexing families, without an
    unstated nonemptiness premise. *)
Theorem borel_separated_countable_unions (T : topologicalType)
    (I J : choiceType) (D : set I) (E : set J) (P : I -> set T) (Q : J -> set T) :
  countable D -> countable E ->
  (forall i j, D i -> E j -> borel_separated (P i) (Q j)) ->
  borel_separated (\bigcup_(i in D) P i) (\bigcup_(j in E) Q j).
Proof.
move=> hD hE hsep.
have hc i j : exists A : set T, borel_set A /\
    (D i -> E j -> P i `<=` A /\ Q j `<=` ~` A).
  case: (pselect (D i /\ E j))=> [[hi hj]|hn].
  - have [A [hA [hP hQ]]] := proj1 (borel_separated_one_separator _ _) (hsep i j hi hj).
    exists A; split=> // _ _; by split.
  - exists set0; split; first exact: open_borel_set (@open0 T).
    by move=> hi hj; exfalso; apply: hn; split.
pose A i j := projT1 (cid (hc i j)).
have hA i j : borel_set (A i j) /\
    (D i -> E j -> P i `<=` A i j /\ Q j `<=` ~` A i j) := projT2 (cid (hc i j)).
pose B i := ~` (\bigcup_(j in E) ~` A i j).
have hB i : borel_set (B i).
  apply: borel_set_complement; apply: borel_set_countable_union hE _.
  move=> j _; apply: borel_set_complement; exact: (hA i j).1.
apply/(proj2 (borel_separated_one_separator _ _)).
exists (\bigcup_(i in D) B i); split.
- apply: borel_set_countable_union hD _; by move=> i _; exact: hB.
- split.
  + move=> x [i hi hx]; exists i=> //.
    move=> [j hj hn]; apply: hn; exact: ((hA i j).2 hi hj).1 x hx.
  + move=> x [j hj hx] [i hi hnot]; apply: hnot.
    exists j=> //; exact: ((hA i j).2 hi hj).2 x hx.
Qed.
