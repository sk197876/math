(** Supporting local form of the uniform-limit argument in Federer 2.3.5, p.
    77 Source context: PartialContinuityUP.v. Only general topology and
    metric neighborhoods are imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [partial_metric_local_continuity]: supporting
    epsilon-neighborhood criterion for continuity of f|C in
    Federer 2.3.5, p. 77. It handles partial maps and empty C. *)
Lemma partial_metric_local_continuity (R : realType)
    (X : topologicalType) (Y : metricType R) (C : set X)
    (f : partial_function X Y) : C `<=` partial_function_domain f ->
  (forall x y, C x -> partial_function_graph f x y -> forall e, 0 < e ->
    exists V, open V /\ V x /\ forall z w, C z -> V z ->
      partial_function_graph f z w -> mdist y w < e) ->
  partial_function_continuous_on C f.
Proof.
move=> hd hl; constructor=> // U hU.
exists ((~` C) `|` partial_function_preimage f U)°; split; first exact: open_interior.
apply/seteqP; split=> x [hx hy]; split=> //.
- have [y [hxy huy]] := hy.
  have hnb : nbhs y U by rewrite openE in hU; exact: hU y huy.
  have [e he heb] := (proj1 (metricType_numDomainType.nbhs_mdistP y U)) hnb.
  have [V [hV [hxV hv]]] := hl x y hx hxy e he.
  have hnv : nbhs x V by rewrite openE in hV; exact: hV x hxV.
  apply: (filterS _ hnv)=> z hz.
  case: (pselect (C z))=> hcz; last by left.
  right; have [w hw] := hd z hcz; exists w; split=> //.
  apply: heb; exact: hv z w hcz hz hw.
- have hh := nbhs_singleton hy; case: hh=> // hn; exfalso; exact: hn hx.
Qed.
