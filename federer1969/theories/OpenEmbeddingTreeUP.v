(** Federer (1969), 2.2.9, p. 65: the open sets U(s) and their closures E(s)
    used to embed the sequence space. Finite words use the reversed storage
    convention of ClosedCoverTreeUP.v, so j::s appends the newest
    coordinate. Unlike the covering tree of 2.2.8, the children here need
    not cover their parent. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import ClosedCoverTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_open_embedding_tree]: Federer 2.2.9,
    p. 65, abstract laws for the tree U(s): each set is open
    and nonempty, each child closure lies in its parent, and
    non-root closures have diameter below 2^(-k-2). Sibling open sets are disjoint, as printed; their closures
    may meet at boundary points, as required for the real-line case. *)
Record is_open_embedding_tree (R : realType) (T : metricType R)
    (U : seq nat -> set T) : Prop := {
  open_embedding_tree_root : U [::] = setT;
  open_embedding_tree_open : forall s, open (U s);
  open_embedding_tree_nonempty : forall s, U s !=set0;
  open_embedding_tree_child_inside : forall s j, closure (U (j::s)) `<=` U s;
  open_embedding_tree_siblings : forall s i j, i <> j ->
    U (i::s) `&` U (j::s) = set0;
  open_embedding_tree_diameter : forall s, s != [::] -> forall x y,
    closure (U s) x -> closure (U s) y -> mdist x y < @closed_cover_tree_scale R (size s)
}.

(** Source for [open_embedding_tree_child_closed_inside]:
    supporting nesting in Federer 2.2.9, p. 65: a child
    closure also lies in its parent's closure. *)
Lemma open_embedding_tree_child_closed_inside (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) s j :
  closure (U (j::s)) `<=` closure (U s).
Proof.
move=> x hx; apply: subset_closure.
exact: (@open_embedding_tree_child_inside R T U hU s j x hx).
Qed.

(** Source for [open_embedding_tree_level_disjoint]: Federer 2.2.9, p. 65,
    disjointness of the open sets at every level. Distinct siblings are
    disjoint by the specification, and children of distinct parents inherit
    disjointness. *)
Lemma open_embedding_tree_level_disjoint (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) s t :
  size s = size t -> s <> t -> U s `&` U t = set0.
Proof.
elim: s t=> [|i s IH] [|j t] /= hsize hne.
- exfalso; exact: hne (erefl _).
- discriminate hsize.
- discriminate hsize.
- have hst : size s = size t by case: hsize.
  case: (eqVneq s t)=> [hst'|hst'].
  + subst t; apply: (@open_embedding_tree_siblings R T U hU s i j).
    move=> hij; apply: hne; by rewrite hij.
  + have hneq : s <> t by move=> heq; move: hst'; rewrite heq eqxx.
    have hd := IH t hst hneq.
    apply/seteqP; split; last by move=> x [].
    move=> x [hxi hxj].
    have hxs := @open_embedding_tree_child_inside R T U hU s i x (subset_closure hxi).
    have hxt := @open_embedding_tree_child_inside R T U hU t j x (subset_closure hxj).
    have hh : (U s `&` U t) x by split.
    by rewrite hd in hh.
Qed.
