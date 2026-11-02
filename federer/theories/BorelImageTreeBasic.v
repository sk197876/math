(** Federer (1969), 2.2.10(2), p. 67: the displayed intersection of level
    unions of B(s) is Borel. Nesting and disjointness force the selected
    level words to be compatible. Only the target topology and abstract
    B-tree laws are used. Source context: BorelImageTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelImageTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_image_tree_level]: direct level union
    in the displayed Borel image T of Federer 2.2.10(2),
    p. 67. Words of length k encode the positive-coordinate
    k-tuples, using natural codes for the entries. *)
Definition borel_image_tree_level (Y : topologicalType) (B : seq nat -> set Y) k :=
  \bigcup_(s in [set s | size s = k]) B s.

(** Source for [borel_image_tree_target]: direct displayed set
    T in Federer 2.2.10(2), p. 67: intersect the unions
    over all words of each positive length. *)
Definition borel_image_tree_target (Y : topologicalType) (B : seq nat -> set Y) :=
  \bigcap_(k : nat) borel_image_tree_level B k.+1.

(** Source for [borel_image_tree_target_borel]: direct Borel assertion for
    the displayed T in Federer 2.2.10(2), p. 67, by countable union and
    intersection closure. *)
Lemma borel_image_tree_target_borel (X : Type) (Y : topologicalType) (f : X -> Y)
    (C : set X) (E A : seq nat -> set X) (B : seq nat -> set Y)
    (hB : is_borel_image_tree f C E A B) : borel_set (borel_image_tree_target B).
Proof.
apply: borel_set_countable_intersection; first exact: countableP.
- by exists 0%N.
- move=> k _; apply: borel_set_countable_union; first exact: countableP.
  move=> s _; exact: (@borel_image_tree_borel X Y f C E A B hB s).
Qed.

(** Source for [borel_image_tree_level_disjoint]: supporting same-level
    disjointness for Federer 2.2.10(2), p. 67: distinct words have either
    disjoint parents or disjoint siblings. *)
Lemma borel_image_tree_level_disjoint (X : Type) (Y : topologicalType) (f : X -> Y)
    (C : set X) (E A : seq nat -> set X) (B : seq nat -> set Y)
    (hB : is_borel_image_tree f C E A B) s t :
  size s = size t -> s <> t -> B s `&` B t = set0.
Proof.
elim: s t=> [|i s IH] [|j t] /= hsize hne; try discriminate.
- by exfalso; apply: hne.
- have hst : size s = size t by case: hsize.
  case: (eqVneq s t)=> h.
  + subst t; apply: (@borel_image_tree_children_disjoint X Y f C E A B hB s i j).
    by move=> hij; apply: hne; rewrite hij.
  + have hneq : s <> t by move=> he; move: h; rewrite he eqxx.
    have hd := IH t hst hneq.
    apply/seteqP; split; last by move=> y [].
    move=> y [hi hj]; have hp : (B s `&` B t) y.
      split.
      * exact: (@borel_image_tree_child_subset X Y f C E A B hB s i y hi).
      * exact: (@borel_image_tree_child_subset X Y f C E A B hB t j y hj).
    by rewrite hd in hp.
Qed.

(** Source for [borel_image_tree_compatible_words]: supporting branch
    recovery for Federer 2.2.10(2), p. 67: a point of the intersection of
    level unions has one compatible word at each length. *)
Lemma borel_image_tree_compatible_words (X : Type) (Y : topologicalType) (f : X -> Y)
    (C : set X) (E A : seq nat -> set X) (B : seq nat -> set Y)
    (hB : is_borel_image_tree f C E A B) y :
  borel_image_tree_target B y -> exists w : nat -> seq nat,
    (forall k, size (w k) = k /\ B (w k) y) /\
    w 0%N = [::] /\ forall k, w k.+1 = head 0%N (w k.+1) :: w k.
Proof.
move=> hy; have hw k : exists s, size s = k /\ B s y.
  case: k=> [|k].
  - exists [::]; split=> //; by rewrite (borel_image_tree_root hB).
  - have [s hs hys] := hy k Logic.I; exists s; by split.
pose w k := projT1 (cid (hw k)).
have hl k : size (w k) = k /\ B (w k) y := projT2 (cid (hw k)).
exists w; split=> //; split.
- apply/eqP; by rewrite -size_eq0 (hl 0%N).1.
- move=> k; have [hsize hmem] := hl k.+1.
  case he : (w k.+1)=> [|j s]; rewrite he /= in hsize hmem; first discriminate.
  have hs : size s = k by case: hsize.
  have hp : B s y := @borel_image_tree_child_subset X Y f C E A B hB s j y hmem.
  have hsw : s = w k.
    case: (eqVneq s (w k))=> h; first exact h.
    exfalso; have hneq : s <> w k by move=> hh; move: h; rewrite hh eqxx.
    have hd := @borel_image_tree_level_disjoint X Y f C E A B hB s (w k)
      (eq_trans hs (esym (hl k).1)) hneq.
    have hh : (B s `&` B (w k)) y by split=> //; exact: (hl k).2.
    by rewrite hd in hh.
  by rewrite /= hsw.
Qed.
