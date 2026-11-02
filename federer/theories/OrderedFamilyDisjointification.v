(** Federer (1969), 2.5.10, p. 101: subtract the union of the predecessors
    from each member of the well-ordered closed family. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP WellOrderLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordered_family_piece]: the subtraction of earlier
    members in Federer 2.5.10, p. 101. Definition of the
    piece of a given indexed set; the ordering is reflexive,
    with strictness recorded by well_order_prefix. *)
Definition ordered_family_piece (X J : choiceType) (D : set J) (r : rel J)
    (B : J -> set X) j := B j `\` (\bigcup_(i in well_order_prefix D r j) B i).

(** Source for [ordered_family_piece_subset]: supporting inclusion
    for Federer 2.5.10, p. 101: a piece lies in its
    original finite-measure closed set. *)
Lemma ordered_family_piece_subset (X J : choiceType) (D : set J) (r : rel J)
    (B : J -> set X) j : ordered_family_piece D r B j `<=` B j.
Proof. by move=> x [hx _]. Qed.

(** Source for [ordered_family_pieces_disjoint]: disjointness
    asserted by the construction in Federer 2.5.10, p. 101.
    The earlier of two distinct indices has been removed from
    the later piece. *)
Lemma ordered_family_pieces_disjoint (X J : choiceType) (D : set J) (r : rel J)
    (B : J -> set X) : well_order r ->
  forall i j, D i -> D j -> i <> j ->
    ordered_family_piece D r B i `&` ordered_family_piece D r B j=set0.
Proof.
move=> hw i j hi hj hne; apply/seteqP; split=> [x [[hxi hni] [hxj hnj]]|x []].
have /orP[hij|hji] := well_order_total_law hw i j.
- apply: hnj; exists i=> //; by split=> //; split.
- apply: hni; exists j=> //; split=> //; split=> //; move=> he; apply: hne; exact: esym he.
Qed.

(** Source for [ordered_family_piece_prefix_cover]: supporting
    coverage in Federer 2.5.10, p. 101. Every point of
    B_i belongs to the piece of the least index whose set contains
    it, and that index is no later than i. *)
Lemma ordered_family_piece_prefix_cover (X J : choiceType) (D : set J) (r : rel J)
    (B : J -> set X) : well_order r -> forall i, D i ->
  B i `<=` (\bigcup_(j in ([set i] `|` well_order_prefix D r i)) ordered_family_piece D r B j).
Proof.
move=> hw i hi x hx.
pose E := [set j | D j /\ B j x].
have hE : exists j, E j by exists i; split.
have [j [[hj hxj] hmin]] := well_order_set_minimum hw hE.
exists j.
- case: (pselect (j = i))=> he; first by left.
  right; split=> //; split=> //; apply: hmin; by split.
- split=> //; move=> [k [hk [hkj hne]] hxk].
  apply: hne; apply: (well_order_antisymmetric_law hw); apply/andP; split=> //.
  apply: hmin; by split.
Qed.
