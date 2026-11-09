(** Federer (1969), 3.4.5, pp. 319–320: Boolean
    identities for the original set germs, proved from sealed laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP LocalGermSealed SetGermUP SetGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section BooleanLaws.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation germ:=(@set_germ X a).
Local Notation join:=(@SetGerms.join X a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation neg:=(@SetGerms.neg X a).

(** Source for [set_germ_has_representative]: a set germ has
    an original representative, 3.4.5, p. 319. *)
Lemma set_germ_has_representative (alpha:G):exists S:set X,germ S=alpha.
Proof.
exact:(@local_germ_representative X Prop [the choiceType of set X] (fun S=>S) a G germ
  (@LocalGerms.laws X Prop [the choiceType of set X] (fun S=>S) a) alpha).
Qed.

(** Source for [set_germ_union_associative]: union is associative
    on set germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_union_associative:associative join.
Proof.
move=>alpha beta gamma.
have [S <-]:=set_germ_has_representative alpha.
have [T <-]:=set_germ_has_representative beta.
have [U <-]:=set_germ_has_representative gamma.
by rewrite !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)) setUA.
Qed.

(** Source for [set_germ_union_commutative]: union is commutative
    on set germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_union_commutative:commutative join.
Proof.
move=>alpha beta.
have [S <-]:=set_germ_has_representative alpha.
have [T <-]:=set_germ_has_representative beta.
by rewrite !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)) setUC.
Qed.

(** Source for [set_germ_intersection_associative]: intersection
    is associative on set germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_intersection_associative:associative meet.
Proof.
move=>alpha beta gamma.
have [S <-]:=set_germ_has_representative alpha.
have [T <-]:=set_germ_has_representative beta.
have [U <-]:=set_germ_has_representative gamma.
by rewrite !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) setIA.
Qed.

(** Source for [set_germ_intersection_commutative]: intersection
    is commutative on set germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_intersection_commutative:commutative meet.
Proof.
move=>alpha beta.
have [S <-]:=set_germ_has_representative alpha.
have [T <-]:=set_germ_has_representative beta.
by rewrite !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) setIC.
Qed.

(** Source for [set_germ_complement_involutive]: taking the
    complement twice preserves the germ, 3.4.5, pp. 319–320. *)
Lemma set_germ_complement_involutive:involutive neg.
Proof.
move=>alpha;have [S <-]:=set_germ_has_representative alpha.
by rewrite !(@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a)) setCK.
Qed.

(** Source for [set_germ_union_empty]: the empty germ is
    the union identity, 3.4.5, pp. 319–320. *)
Lemma set_germ_union_empty:right_id (germ set0) join.
Proof.
move=>alpha;have [S <-]:=set_germ_has_representative alpha.
by rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)) setU0.
Qed.

(** Source for [set_germ_intersection_whole]: the whole-space
    germ is the intersection identity, 3.4.5, pp. 319–320. *)
Lemma set_germ_intersection_whole:right_id (germ setT) meet.
Proof.
move=>alpha;have [S <-]:=set_germ_has_representative alpha.
by rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) setIT.
Qed.

(** Source for [set_germ_union_complement]: the union of a germ
    and its complement is the whole germ, 3.4.5, pp. 319–320. *)
Lemma set_germ_union_complement:left_inverse (germ setT) neg join.
Proof.
move=>alpha;have [S <-]:=set_germ_has_representative alpha.
by rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)) setUCl.
Qed.

(** Source for [set_germ_intersection_complement]: the intersection
    with the complementary germ is empty, 3.4.5, pp. 319–320. *)
Lemma set_germ_intersection_complement:left_inverse (germ set0) neg meet.
Proof.
move=>alpha;have [S <-]:=set_germ_has_representative alpha.
by rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) setICl.
Qed.

(** Source for [set_germ_distributive]: intersection distributes
    over union of germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_distributive:left_distributive meet join.
Proof.
move=>alpha beta gamma.
have [S <-]:=set_germ_has_representative alpha.
have [T <-]:=set_germ_has_representative beta.
have [U <-]:=set_germ_has_representative gamma.
rewrite !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
by rewrite setIUl.
Qed.
End BooleanLaws.
