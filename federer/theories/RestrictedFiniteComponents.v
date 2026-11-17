(** Federer (1969), 3.4.8(11), p. 335:
    combine the original component homeomorphisms of
    (10) with finite fibres. Every restricted
    component projects onto a base component, so
    a finite base component family bounds the
    entire restricted source component family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground HomeomorphismUP
  ComponentHomeomorphismRestriction FiniteFibreComponentCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [restricted_finite_components]:
    the exact component-count assembly for the
    original T in 3.4.8(11), p. 335.
    All geometric inputs are the previously proved
    original model conclusions; no new sheet construction
    or inverse-function argument is needed. *)
Theorem restricted_finite_components (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V W:set Y) (y0:Y):
  continuous P ->W `<=` V ->
  (forall y,V y ->open (connected_component V y)) ->
  (forall x,Z x ->exists F:metric_subset (connected_component Z x)->
      metric_subset (connected_component V (P x)),
    (forall a,val (F a) = P (val a)) /\is_homeomorphism F) ->
  (forall y,finite_set [set x|Z x /\P x = y]) ->
  finite_set (connected_component W @` W) ->
  finite_set (connected_component (Z `&` (P @^-1` W)) @` (Z `&` (P @^-1` W))).
Proof.
move=>hP hWV hOpen hHomeomorphisms hFibres hBase.
pose D:=Z `&` (P @^-1` W).
apply:(@finite_fibre_component_count X Y P D W y0 _ hBase).
- by move=>x [_ hx].
- move=>y _;apply:(sub_finite_set _ (hFibres y)).
  by move=>x [[hx _] hPx];split.
- move=>x [hx hWx].
  exact:(@component_homeomorphism_restriction_image R X Y P Z V W
    hP hWV hOpen hHomeomorphisms x hx hWx).
Qed.
