(** Federer (1969), 2.2.8, p. 64: the family E(s1,...,sk) of nonempty closed
    sets, with diameter at most 2^(-k-2), each covered by its children. We
    specify the tree abstractly before constructing it. Internally finite
    words are stored in reverse order: j::s appends the newest coordinate to
    the book's word. This permits ordinary structural recursion and does not
    change the represented prefix or level. Source context:
    MetricClosedBalls.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_cover_tree_scale]: Federer 2.2.8,
    p. 64, the printed diameter bound 2^(-k-2) for words of
    length k. The root has no imposed diameter bound. *)
Definition closed_cover_tree_scale (R : realType) (k : nat) : R := (2^-1)^+(k+2).

(** Source for [is_closed_cover_tree]: Federer 2.2.8, p. 64, abstract laws
    of the displayed family E: closedness, nonemptiness, covering by
    children, and shrinking diameters. The empty word denotes X. *)
Record is_closed_cover_tree (R : realType) (T : metricType R)
    (E : seq nat -> set T) : Prop := {
  closed_cover_tree_root : E [::] = setT;
  closed_cover_tree_closed : forall s, closed (E s);
  closed_cover_tree_nonempty : forall s, E s !=set0;
  closed_cover_tree_children : forall s, E s = \bigcup_j E (j::s);
  closed_cover_tree_diameter : forall s, s != [::] -> forall x y,
    E s x -> E s y -> mdist x y <= @closed_cover_tree_scale R (size s)
}.

(** Source for [closed_cover_tree_child_subset]: supporting
    nesting consequence of the child-cover identity in Federer
    2.2.8, p. 64: every child is contained in its parent. *)
Lemma closed_cover_tree_child_subset (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E) s j :
  E (j::s) `<=` E s.
Proof. move=> x hx; rewrite (closed_cover_tree_children hE s); by exists j. Qed.

(** Source for [closed_cover_tree_scale_positive]: supporting
    positivity of the radii used to construct Federer's E(s),
    2.2.8, p. 64. *)
Lemma closed_cover_tree_scale_positive (R : realType) k : 0 < @closed_cover_tree_scale R k.
Proof. by rewrite /closed_cover_tree_scale exprn_gt0 ?invr_gt0 ?ltr0n. Qed.
