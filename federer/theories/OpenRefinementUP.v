(** Federer (1969), 2.2.9, p. 65: a countable disjoint family of nonempty
    open children with small closures inside a parent. This specification
    includes the diameter control required by the subsequent tree
    construction. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_open_disjoint_refinement]: supporting abstract
    child-family laws for Federer 2.2.9, p. 65: open and
    nonempty children, closures contained in the parent, pairwise
    disjoint closures, and strict diameter bound e. Pairwise disjoint
    closures strengthen the printed disjointness and suffice for it. *)
Record is_open_disjoint_refinement (R : realType) (T : metricType R)
    (U : set T) (e : R) (F : nat -> set T) : Prop := {
  open_refinement_open : forall n, open (F n);
  open_refinement_nonempty : forall n, F n !=set0;
  open_refinement_inside : forall n, closure (F n) `<=` U;
  open_refinement_disjoint : forall i j, i <> j -> closure (F i) `&` closure (F j) = set0;
  open_refinement_diameter : forall n x y, closure (F n) x -> closure (F n) y -> mdist x y < e
}.

(** Source for [open_refinement_children_distinct]: Supporting Federer
    2.2.9, p. 65. *)
Lemma open_refinement_children_distinct (R : realType) (T : metricType R)
    (U : set T) e (F : nat -> set T) (hF : is_open_disjoint_refinement U e F) :
  injective F.
Proof.
move=> i j he; case: (eqVneq i j)=> [//|hne].
exfalso; have [x hx] := open_refinement_nonempty hF i.
have hxi : closure (F i) x := subset_closure hx.
have hxj : closure (F j) x by rewrite -he.
have hneq : i <> j by move=> heq; move: hne; rewrite heq eqxx.
have hd := @open_refinement_disjoint R T U e F hF i j hneq.
have hh : (closure (F i) `&` closure (F j)) x by split.
by rewrite hd in hh.
Qed.
