(** Private finite rectangular difference construction supporting
    Federer (1969), 2.8.20, p. 152; Saks1934
    Lemma B, p. 258, and Cesari1939 Lemma III,
    p. 306. Cut each coordinate into lower, middle
    and upper regions relative to the removed box, then
    discard the middle-middle cell and all empty cells.
    Downstream packing uses only the partition laws, not
    this grid construction. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals.
From Federer Require Import HalfOpenIntervalRegions ScalarHalfOpenRectangles FiniteHalfOpenPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [half_open_difference_cell]: private grid
    cell in the finite difference decomposition supporting
    Federer 2.8.20, p. 152. Its indices record
    the two coordinates' positions relative to the removed box. *)
Definition half_open_difference_cell (R : realType) (a b c d u v w z : R)
    (tag : option bool * option bool) :=
  scalar_half_open_rectangle
    (interval_cut_lower_endpoint a u v tag.1) (interval_cut_upper_endpoint b u v tag.1)
    (interval_cut_lower_endpoint c w z tag.2) (interval_cut_upper_endpoint d w z tag.2).

(** Source for [half_open_difference_cell_membership]: supporting
    membership law for the private difference grid used for
    Federer 2.8.20, p. 152. It separates parent
    membership from the two region tests. *)
Lemma half_open_difference_cell_membership (R : realType) (a b c d u v w z : R)
    (tag : option bool * option bool) (p : R*R) :
  half_open_difference_cell a b c d u v w z tag p <->
  scalar_half_open_rectangle a b c d p /\
    interval_cut_region u v tag.1 p.1 /\ interval_cut_region w z tag.2 p.2.
Proof.
rewrite /half_open_difference_cell /scalar_half_open_rectangle /=.
rewrite !interval_cut_cellE; split.
- move=> [/andP [hx hc] /andP [hy hd]]; split; [by split|by split].
- move=> [[hx hy] [hc hd]]; split; by rewrite ?hx ?hy ?hc ?hd.
Qed.

(** Source for [nonempty_difference_cell_rectangle]: nonempty
    grid cells have positive side lengths in the finite
    construction supporting Federer 2.8.20, p. 152. *)
Lemma nonempty_difference_cell_rectangle (R : realType) (a b c d u v w z : R)
    (tag : option bool * option bool) :
  half_open_difference_cell a b c d u v w z tag !=set0 ->
  is_nondegenerate_half_open_rectangle (half_open_difference_cell a b c d u v w z tag).
Proof.
move=> [[x y] hx].
move: hx; rewrite /half_open_difference_cell /scalar_half_open_rectangle /= !in_itv /=.
move=> [/andP [hx1 hx2] /andP [hy1 hy2]].
exists (interval_cut_lower_endpoint a u v tag.1), (interval_cut_upper_endpoint b u v tag.1),
  (interval_cut_lower_endpoint c w z tag.2), (interval_cut_upper_endpoint d w z tag.2).
split; first exact: le_lt_trans hx1 hx2.
split; first exact: le_lt_trans hy1 hy2.
by [].
Qed.

(** Source for [half_open_rectangle_difference_partition_exists]:
    existence of the finite disjoint remaining regions needed
    in the Bohr construction supporting Federer 2.8.20,
    p. 152. Both input boxes have positive side
    lengths; empty output cells are removed. The witness
    remains inside this opaque existence proof. *)
Theorem half_open_rectangle_difference_partition_exists (R : realType) (A B : set (R*R)) :
  is_nondegenerate_half_open_rectangle A -> is_nondegenerate_half_open_rectangle B ->
  exists G, is_finite_half_open_partition (A `\` B) G.
Proof.
move=> [a [b [c [d [hab [hcd ->]]]]]] [u [v [w [z [huv [hwz ->]]]]]].
pose C := half_open_difference_cell a b c d u v w z.
pose D := [set tag : option bool * option bool | tag <> (None,None) /\ C tag !=set0].
pose G := C @` D.
have hmem tag p := @half_open_difference_cell_membership R a b c d u v w z tag p.
exists G; constructor.
- exact (@finite_image _ _ D C (@finite_finset _ D)).
- move=> S [tag [_ hn] <-]; exact: nonempty_difference_cell_rectangle hn.
- move=> S T [s _ <-] [t _ <-] hne; apply/seteqP; split=> [p [hs ht]|p []].
  have [_ [hs1 hs2]] := (hmem s p).1 hs.
  have [_ [ht1 ht2]] := (hmem t p).1 ht.
  have he1 := @interval_cut_region_unique R u v p.1 s.1 t.1 huv hs1 ht1.
  have he2 := @interval_cut_region_unique R w z p.2 s.2 t.2 hwz hs2 ht2.
  have he : s = t := @injective_projections (option bool) (option bool) s t he1 he2.
  exfalso; apply: hne; by rewrite he.
- apply/seteqP; split.
  + move=> p [S [tag [hne _] <-] hp].
    have [hA [hc1 hc2]] := (hmem tag p).1 hp.
    split=> // hB; apply: hne.
    have hb1 : interval_cut_region u v None p.1 := hB.1.
    have hb2 : interval_cut_region w z None p.2 := hB.2.
    have he1 := @interval_cut_region_unique R u v p.1 tag.1 None huv hc1 hb1.
    have he2 := @interval_cut_region_unique R w z p.2 tag.2 None hwz hc2 hb2.
    exact (@injective_projections (option bool) (option bool) tag (None,None) he1 he2).
  + move=> p [hA hnB].
    have [s hs] := @interval_cut_region_exists R u v p.1 huv.
    have [t ht] := @interval_cut_region_exists R w z p.2 hwz.
    have hp : C (s,t) p by apply: (hmem (s,t) p).2; split=> //; split.
    have hne : (s,t) <> (None,None).
      move=> he; have hes : s = None := congr1 fst he.
      have het : t = None := congr1 snd he.
      rewrite hes het in hs ht; apply: hnB; by split.
    exists (C (s,t)); last exact hp.
    exists (s,t)=> //; split=> //; by exists p.
Qed.
