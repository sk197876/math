(** Federer (1969), 2.2.10, pp. 66–67, Borel separation. Source context and
    erratum conventions: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_separated]: direct definition in Federer 2.2.10, p.
    66, last paragraph: P and Q are contained in disjoint Borel sets A and
    B. No separation axiom on the ambient topology is required. *)
Definition borel_separated (T : topologicalType) (P Q : set T) : Prop :=
  exists A B, borel_set A /\ borel_set B /\ P `<=` A /\ Q `<=` B /\ A `&` B = set0.

(** Source for [borel_separated_one_separator]: supporting
    equivalent formulation for Federer 2.2.10, pp. 66–67:
    one Borel set contains P and its complement contains Q.
    Borel complement closure supplies the second separator. *)
Lemma borel_separated_one_separator (T : topologicalType) (P Q : set T) :
  borel_separated P Q <-> exists A, borel_set A /\ P `<=` A /\ Q `<=` ~` A.
Proof.
split.
- move=> [A [B [hA [hB [hPA [hQB hdis]]]]]].
  exists A; split=> //; split=> // x hx hAx.
  have hh : (A `&` B) x by split=> //; exact: hQB x hx.
  by rewrite hdis in hh.
- move=> [A [hA [hPA hQA]]]; exists A, (~` A).
  split=> //; split; first exact: borel_set_complement hA.
  split=> //; split=> //; exact: setICr.
Qed.

(** Source for [borel_separated_symmetric]: elementary symmetry
    supporting the Borel-separation argument in Federer 2.2.10,
    pp. 66–67: interchange the two Borel supersets. *)
Lemma borel_separated_symmetric (T : topologicalType) (P Q : set T) :
  borel_separated P Q -> borel_separated Q P.
Proof.
move=> [A [B [hA [hB [hPA [hQB hdis]]]]]].
exists B, A; split=> //; split=> //; split=> //; split=> //.
by rewrite setIC.
Qed.

(** Source for [borel_separated_subsets]: supporting monotonicity
    in Federer 2.2.10, pp. 66–67: subsets of two Borel-
    separated sets are separated by the same Borel supersets. *)
Lemma borel_separated_subsets (T : topologicalType) (P Q P' Q' : set T) :
  P' `<=` P -> Q' `<=` Q -> borel_separated P Q -> borel_separated P' Q'.
Proof.
move=> hp hq [A [B [hA [hB [hPA [hQB hdis]]]]]].
exists A, B; split=> //; split=> //; split; first exact: subset_trans hp hPA.
split=> //; exact: subset_trans hq hQB.
Qed.

(** Source for [borel_separated_disjoint]: supporting necessary
    disjointness in Federer 2.2.10, pp. 66–67: sets lying
    in disjoint Borel supersets cannot share a point. *)
Lemma borel_separated_disjoint (T : topologicalType) (P Q : set T) :
  borel_separated P Q -> P `&` Q = set0.
Proof.
move=> [A [B [_ [_ [hPA [hQB hdis]]]]]].
apply/seteqP; split; last by move=> x [].
move=> x [hp hq]; have hh : (A `&` B) x by split; [exact: hPA x hp|exact: hQB x hq].
by rewrite hdis in hh.
Qed.

(** Source for [borel_separated_empty_left]: supporting empty-set
    case in Federer 2.2.10, pp. 66–67: the empty set is
    separated from any set by the Borel sets empty and whole. *)
Lemma borel_separated_empty_left (T : topologicalType) (Q : set T) :
  borel_separated set0 Q.
Proof.
apply/(proj2 (borel_separated_one_separator _ _)); exists set0.
split; first exact: open_borel_set (@open0 T).
by split=> // x _ [].
Qed.
