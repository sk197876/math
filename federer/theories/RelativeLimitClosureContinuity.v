(** Federer (1969), 2.4.17, p. 90: continuity on the closure of the
    finite-norm exponent set. These supporting general-topology lemmas make
    the passage to continuity on the entire closure explicit. The target is
    used only through closed-neighborhood refinement. No norm-continuity
    theorem is imported. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_limit_preserves_local_closed_range]: supporting
    closed-range argument for the closure in Federer 2.4.17, p. 90 *)
Lemma relative_limit_preserves_local_closed_range (T Z : topologicalType)
    (A O : set T) (C : set Z) (f : T -> Z) (x : T) :
  closure A x -> open O -> O x -> closed C ->
  (forall y, A y -> O y -> C (f y)) ->
  (forall B, nbhs (f x) B -> exists W, nbhs x W /\ forall y, A y -> W y -> B (f y)) ->
  C (f x).
Proof.
move=> hx hO hxO hC hrange hl; apply: contrapT=> hnot.
have hcomp : open (~` C) := closed_openC hC.
have hnb : nbhs (f x) (~` C) by rewrite openE in hcomp; exact: hcomp (f x) hnot.
have [W [hW hFW]] := hl _ hnb.
have hOnb : nbhs x O by rewrite openE in hO; exact: hO x hxO.
have hmeet : nbhs x (O `&` W) by apply: filterI.
have [y [hy [hyO hyW]]] := hx _ hmeet.
exact: (hFW y hy hyW) (hrange y hy hyO).
Qed.

(** Source for [relative_limits_continuous_on_closure]: supporting
    dense-domain extension principle for Federer 2.4.17, p. 90 Values at all
    closure points are specified by the same relative limits, so no new
    extension function or existence axiom is assumed. *)
Theorem relative_limits_continuous_on_closure (T Z : topologicalType)
    (A : set T) (f : T -> Z) :
  (forall (z : Z) (B : set Z), nbhs z B -> exists C, closed C /\ nbhs z C /\ C `<=` B) ->
  (forall x, closure A x -> forall B, nbhs (f x) B ->
    exists W, nbhs x W /\ forall y, A y -> W y -> B (f y)) ->
  continuous (f : subspace (closure A) -> Z).
Proof.
move=> hregular hl; apply/subspace_continuousP=> x hx B hB.
have [C [hC [hCx hCB]]] := hregular (f x) B hB.
have [W [hW hFW]] := hl x hx C hCx.
rewrite nbhsE in hW; have [O [hO hxO] hOW] := hW.
change (nbhs x [set y | closure A y -> B (f y)]).
rewrite nbhsE; exists O; first by split.
move=> y hy hyA.
apply: hCB.
apply: (@relative_limit_preserves_local_closed_range T Z A O C f y hyA hO hy hC).
- move=> z hz hzO; exact: hFW z hz (hOW z hzO).
- exact: hl y hyA.
Qed.
