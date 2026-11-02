(** Federer (1969), 2.2.10, p. 67: elementary consequences used to choose a
    pair of branches whose images fail to be Borel separated. Both family
    operations are unions, as corrected in Federer's erratum p. 1, book p.
    67 line 2. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelSeparation BorelSeparationFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [non_borel_separated_nonempty]: supporting nonemptiness
    observation in Federer 2.2.10, p. 67: failure of Borel separation forces
    both sets to be nonempty. *)
Lemma non_borel_separated_nonempty (T : topologicalType) (P Q : set T) :
  ~ borel_separated P Q -> P !=set0 /\ Q !=set0.
Proof.
move=> hn; split; apply: contrapT=> he; apply: hn.
- have hp : P = set0 by apply/seteqP; split=> [x hx|x []]; exfalso; apply: he; by exists x.
  rewrite hp; exact: borel_separated_empty_left.
- have hq : Q = set0 by apply/seteqP; split=> [x hx|x []]; exfalso; apply: he; by exists x.
  rewrite hq; apply: borel_separated_symmetric; exact: borel_separated_empty_left.
Qed.

(** Source for [non_borel_separated_sequence_refinement]: supporting
    child-pair choice in Federer 2.2.10, p. 67: if two sequence unions fail
    to be separated, some pair of sequence members fails to be separated. *)
Lemma non_borel_separated_sequence_refinement (T : topologicalType)
    (P Q : nat -> set T) :
  ~ borel_separated (\bigcup_i P i) (\bigcup_j Q j) ->
  exists i j, ~ borel_separated (P i) (Q j).
Proof.
move=> hn; apply: contrapT=> hall; apply: hn.
have hc : countable (@setT nat) by exact: countableP.
have hs i j : setT i -> setT j -> borel_separated (P i) (Q j).
  move=> _ _; apply: contrapT=> hij; apply: hall; by exists i,j.
exact (@borel_separated_countable_unions T _ _ setT setT P Q hc hc hs).
Qed.

(** Source for [disjoint_open_borel_separators]: supporting final
    contradiction in Federer 2.2.10, p. 67: containment in disjoint open
    neighborhoods gives Borel separation. *)
Lemma disjoint_open_borel_separators (T : topologicalType) (P Q U V : set T) :
  open U -> open V -> U `&` V = set0 -> P `<=` U -> Q `<=` V ->
  borel_separated P Q.
Proof.
move=> hU hV hd hp hq; exists U,V; split; first exact: open_borel_set hU.
split; first exact: open_borel_set hV.
by split=> //; split.
Qed.
