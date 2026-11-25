(** Federer (1969), 2.2.17, p. 72, open outer approximation of image
    measures. This replaces Federer's countable compact-slab construction by
    the closed-map argument, while the final book theorem retains its
    printed hypotheses. this source typo is separate from Federer's erratum.
    Source context: ProperMapUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import ProperMapUP ProperContinuousClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [proper_outer_open_neighborhood]: supporting neighborhood
    construction for Federer 2.2.17, p. 72. *)
Lemma proper_outer_open_neighborhood (X Y : topologicalType) (f : X -> Y)
    (B : set Y) (U : set X) :
  (forall C, closed C -> closed (f @` C)) -> open U -> f @^-1` B `<=` U ->
  exists W : set Y, open W /\ B `<=` W /\ f @^-1` W `<=` U.
Proof.
move=> hc hU hBU.
exists (~` (f @` (~` U))); split.
- apply: closed_openC; apply: hc; exact: open_closedC hU.
- split.
  + move=> y hy [x hx hxy]; apply: hx; apply: (hBU x); change (B (f x)); by rewrite hxy.
  + move=> x hx; case: (pselect (U x))=> hu; first exact hu.
    exfalso; apply: hx; by exists x.
Qed.
