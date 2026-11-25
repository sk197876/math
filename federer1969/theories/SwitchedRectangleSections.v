(** Federer (1969), 2.6.3(3), p. 118: the set S switches between A1 and A2
    as the second coordinate moves between B and its complement. our
    convention follows Federer. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [switched_rectangle_set]: direct set S
    in Federer 2.6.3(3), p. 118. *)
Definition switched_rectangle_set (X Y : Type) (A1 A2 : set X) (B : set Y) :=
  (A1 `*` B) `|` (A2 `*` ~` B).

(** Source for [switched_horizontal_section_on]: supporting
    section S at y in B in Federer 2.6.3(3), p. 118. *)
Lemma switched_horizontal_section_on (X Y : Type) (A1 A2 : set X) (B : set Y) y :
  B y -> product_horizontal_section (switched_rectangle_set A1 A2 B) y = A1.
Proof.
move=> hy; apply/seteqP; split=> x.
- move=> [[hx _]|[_ hn]]=> //; by exfalso; apply: hn.
- move=> hx; left; by split.
Qed.

(** Source for [switched_horizontal_section_off]: supporting
    section S at y outside B in Federer 2.6.3(3), p. 118. *)
Lemma switched_horizontal_section_off (X Y : Type) (A1 A2 : set X) (B : set Y) y :
  ~ B y -> product_horizontal_section (switched_rectangle_set A1 A2 B) y = A2.
Proof.
move=> hy; apply/seteqP; split=> x.
- move=> [[_ hB]|[hx _]]=> //; by exfalso; apply: hy.
- move=> hx; right; by split.
Qed.

(** Source for [switched_rectangle_intersection]: direct identity
    S intersection T = A1 times B in Federer 2.6.3(3),
    p. 118, using disjointness of A1 and A2. *)
Lemma switched_rectangle_intersection (X Y : Type) (A1 A2 : set X) (B : set Y) :
  (forall x, A1 x -> A2 x -> False) ->
  switched_rectangle_set A1 A2 B `&` (A1 `*` setT) = A1 `*` B.
Proof.
move=> hd; apply/seteqP; split=> [[x y] [[[hx hy]|[hx hy]] [hx1 _]]|[x y] [hx hy]].
- by split.
- by exfalso; exact: hd hx1 hx.
- split; first by left; split.
  by split.
Qed.

(** Source for [rectangle_horizontal_section_on]: supporting
    section of S intersection T in Federer 2.6.3(3), p. 118. *)
Lemma rectangle_horizontal_section_on (X Y : Type) (A : set X) (B : set Y) y :
  B y -> product_horizontal_section (A `*` B) y = A.
Proof. move=> hy; apply/seteqP; split=> [x [hx _]|x hx] //; by split. Qed.

(** Source for [rectangle_horizontal_section_off]: supporting
    empty section of S intersection T in Federer 2.6.3(3), p. 118. *)
Lemma rectangle_horizontal_section_off (X Y : Type) (A : set X) (B : set Y) y :
  ~ B y -> product_horizontal_section (A `*` B) y = set0.
Proof. move=> hy; apply/seteqP; split=> [x [_ hx]|x []]; exact: hy hx. Qed.
