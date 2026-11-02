(** Federer (1969), 2.2.10(1), p. 67: sealed existence of the inseparable
    closed branches used in the contradiction proof. The recursive pair
    choices stay private. Source context and direct-refinement convention:
    InseparableClosedBranchesUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import BorelSeparation InseparableClosedBranchesUP
  InseparableBranchIterationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type InseparableClosedBranchesSignature.
(** Source for [value]: abstract branch witnesses in the assumed
    failure of separation in Federer 2.2.10(1), p. 67. *)
Parameter value : forall (R : realType) (T : metricType R) (Y : topologicalType)
  (f : T -> Y) (H : set T), countable H -> dense H ->
  forall C D : set T, closed C -> closed D ->
  ~ borel_separated (f @` C) (f @` D) -> ((nat -> set T) * (nat -> set T))%type.
(** Source for [laws]: the chosen witnesses satisfy all branch
    laws for Federer 2.2.10(1), p. 67; there is no exposed
    dependence on a particular small-cover or recursive implementation. *)
Parameter laws : forall (R : realType) (T : metricType R) (Y : topologicalType)
  (f : T -> Y) (H : set T) (hc : countable H) (hd : dense H)
  (C D : set T) (hC : closed C) (hD : closed D)
  (hn : ~ borel_separated (f @` C) (f @` D)),
  is_inseparable_closed_branches f C D
    (@value R T Y f H hc hd C D hC hD hn).1
    (@value R T Y f H hc hd C D hC hD hn).2.
End InseparableClosedBranchesSignature.
Module InseparableClosedBranches : InseparableClosedBranchesSignature.
(** Source for [value]: private selection from the proved branch
    existence theorem for Federer 2.2.10(1), p. 67. *)
Definition value (R : realType) (T : metricType R) (Y : topologicalType)
    (f : T -> Y) (H : set T) (hc : countable H) (hd : dense H)
    (C D : set T) (hC : closed C) (hD : closed D)
    (hn : ~ borel_separated (f @` C) (f @` D)) :=
  let P := cid (@inseparable_closed_branches_exists R T Y f H hc hd C D hC hD hn) in
  let Q := cid (projT2 P) in (projT1 P,projT1 Q).
(** Source for [laws]: the privately selected branches obey the
    abstract laws for Federer 2.2.10(1), p. 67. *)
Lemma laws (R : realType) (T : metricType R) (Y : topologicalType)
    (f : T -> Y) (H : set T) (hc : countable H) (hd : dense H)
    (C D : set T) (hC : closed C) (hD : closed D)
    (hn : ~ borel_separated (f @` C) (f @` D)) :
  is_inseparable_closed_branches f C D
    (@value R T Y f H hc hd C D hC hD hn).1
    (@value R T Y f H hc hd C D hC hD hn).2.
Proof.
exact: projT2 (cid (projT2 (cid
  (@inseparable_closed_branches_exists R T Y f H hc hd C D hC hD hn)))).
Qed.
End InseparableClosedBranches.
