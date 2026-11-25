(** Federer (1969), 2.6.2(3), p. 115: the two coordinate sections of a set
    in a Cartesian product. The elementary set identities below support the
    countable unions and intersections in the proof on pp. 116–117; they are
    not separate numbered claims in Federer. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_vertical_section]: direct set {y : (x,y) belongs to
    S} in Federer 2.6.2(3), p. 115 *)
Definition product_vertical_section (X Y : Type) (S : set (X * Y)) (x : X) : set Y :=
  [set y | S (x,y)].

(** Source for [product_horizontal_section]: direct set {x : (x,y) belongs
    to S} in Federer 2.6.2(3), p. 115 *)
Definition product_horizontal_section (X Y : Type) (S : set (X * Y)) (y : Y) : set X :=
  [set x | S (x,y)].

(** Source for [product_vertical_rectangle_on]: supporting
    section calculation for the rectangle repeated integral in
    Federer 2.6.2, p. 116, when x belongs to the first factor. *)
Lemma product_vertical_rectangle_on (X Y : Type) (A : set X) (B : set Y) x :
  A x -> product_vertical_section (A `*` B) x = B.
Proof. move=> hx; apply/seteqP; split=> [y [_ hy]|y hy] //; by split. Qed.

(** Source for [product_vertical_rectangle_off]: supporting
    empty-section case in the rectangle calculation of Federer
    2.6.2, p. 116. *)
Lemma product_vertical_rectangle_off (X Y : Type) (A : set X) (B : set Y) x :
  ~ A x -> product_vertical_section (A `*` B) x = set0.
Proof. move=> hx; apply/seteqP; split=> [y [hy _]|y []]; exact: hx hy. Qed.

(** Source for [product_vertical_union]: supporting fact that
    taking a section commutes with the countable unions used
    in Federer 2.6.2, pp. 115–117. The identity itself
    holds for arbitrary index sets. *)
Lemma product_vertical_union (X Y J : Type) (D : set J) (S : J -> set (X * Y)) x :
  product_vertical_section (\bigcup_(j in D) S j) x =
  \bigcup_(j in D) product_vertical_section (S j) x.
Proof. by []. Qed.

(** Source for [product_vertical_intersection]: supporting
    section identity for the intersections defining P2 in
    Federer 2.6.2, p. 116. The identity itself holds
    for arbitrary, including empty, index sets. *)
Lemma product_vertical_intersection (X Y J : Type) (D : set J) (S : J -> set (X * Y)) x :
  product_vertical_section (\bigcap_(j in D) S j) x =
  \bigcap_(j in D) product_vertical_section (S j) x.
Proof. by []. Qed.

(** Source for [product_vertical_difference]: supporting section identity
    for the null difference W minus S in Federer 2.6.2, p. 117 *)
Lemma product_vertical_difference (X Y : Type) (S T : set (X * Y)) x :
  product_vertical_section (S `\` T) x =
  product_vertical_section S x `\` product_vertical_section T x.
Proof. by []. Qed.
