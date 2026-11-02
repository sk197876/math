(** Federer (1969), 2.9.24, p. 169: the values of a sufficiently fine step
    approximation are close to f at each continuity point. We use full
    continuity points; their BV exceptional set is countable by 2.5.16, p.
    109. The local Federer erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import RealMetricBackground StieltjesSums TaggedStepFunction TaggedStepSampling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [tagged_step_continuity_error]: supporting local
    mesh-to-error estimate in Federer 2.9.24, p. 169.
    The cutoff depends on f, its continuity point and epsilon;
    every ordered tagged partition below that mesh qualifies. *)
Lemma tagged_step_continuity_error (R : realType) (f : R -> R) (x e : R) :
  (f : real_line_metric R -> real_line_metric R) @ (x : real_line_metric R) -->
    (f x : real_line_metric R) -> 0<e ->
  exists d : R, 0<d /\ forall w : seq R,
    sorted <=%O w -> odd (size w) -> tagged_mesh_lt d w ->
    head 0 w<x -> x<=last 0 w -> `|tagged_step_function f w x-f x|<e.
Proof.
move=> hc he.
have hb : nbhs (x : real_line_metric R)
    [set y | ball (f x : real_line_metric R) e (f y)].
  exact: (cvg_ballP _ _).1 hc e he.
have [d hd hnear] := (nbhs_ballP (x : real_line_metric R) _).1 hb.
exists d; split=> // w hs ho hm hax hxb.
have [r [_ [hr hv]]] := @tagged_step_function_nearby_sample R f w d hs ho hm x hax hxb.
have hxr : ball (x : real_line_metric R) d r by rewrite /ball /= distrC.
have hvalue := hnear r hxr.
by move: hvalue; rewrite /ball /= distrC -hv.
Qed.
