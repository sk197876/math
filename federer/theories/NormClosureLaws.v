(** Topological support for Federer (1969), 2.3.8, p. 78, separable linear
    spans Source context: ClosedLinearSpanUP.v. We prove closure stability
    from the previously established norm topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_closed_target_extension]: supporting
    extension from a set to its closure for Federer 2.3.8,
    p. 78: a continuous map landing in a closed set on A
    also lands there on the closure of A. *)
Lemma continuous_closed_target_extension (T U : topologicalType)
    (f : T -> U) (A : set T) (B : set U) :
  continuous f -> closed B -> (forall x, A x -> B (f x)) ->
  forall x, closure A x -> B (f x).
Proof.
move=> hf hB hAB x hx.
have hp : closed (f @^-1` B).
  apply: preimage_closed=> // y _; exact: hf y.
exact: hp x (@closureS T A (f @^-1` B) hAB x hx).
Qed.

(** Source for [dense_closed_superset_all]: supporting density
    principle for the real-scalar closure step in Federer 2.3.8,
    p. 78: a closed superset of a dense set is the whole space. *)
Lemma dense_closed_superset_all (T : topologicalType) (D A : set T) :
  dense D -> closed A -> D `<=` A -> forall x, A x.
Proof.
move=> hd hc hi x; apply: contrapT=> hn.
have hne : (~` A) !=set0 by exists x.
have [y [hy hD]] := hd (~` A) hne (closed_openC hc).
exact: hy (hi y hD).
Qed.

(** Source for [real_norm_metric_translate_continuous]: supporting
    continuity of translation for the separable-span argument in
    Federer 2.3.8, p. 78. *)
Lemma real_norm_metric_translate_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : V) :
  continuous (fun x : real_norm_metric_space hN => (a+x : real_norm_metric_space hN)).
Proof.
have h01 : (0 : R) <= 1 by exact: ler01.
apply: (@metric_fixed_lipschitz_continuous R
  [the metricType R of real_norm_metric_space hN]
  [the metricType R of real_norm_metric_space hN]
  (fun x => a+x) 1 h01).
move=> x y; change (N (a+x-(a+y)) <= 1*N (x-y)).
by rewrite opprD addrACA subrr add0r mul1r.
Qed.

(** Source for [norm_closure_add_stable]: supporting additive stability of
    the closed rational hull in Federer 2.3.8, p. 78 *)
Lemma norm_closure_add_stable (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (A : set (real_norm_metric_space hN)) :
  (forall x y, A x -> A y -> A (x+y)) ->
  forall x y, closure A x -> closure A y -> closure A (x+y).
Proof.
move=> hadd.
have hfirst a (ha : A a) : forall y, closure A y -> closure A (a+y).
  apply: (@continuous_closed_target_extension
    [the topologicalType of real_norm_metric_space hN]
    [the topologicalType of real_norm_metric_space hN] (fun y => a+y) A (closure A)).
  - exact: real_norm_metric_translate_continuous.
  - exact: closed_closure.
  - move=> y hy; apply: subset_closure; exact: hadd ha hy.
move=> x y hx hy.
have hc : continuous (fun a : real_norm_metric_space hN => (a+y : real_norm_metric_space hN)).
  have -> : (fun a : real_norm_metric_space hN => a+y) = (fun a => y+a).
    by apply: funext=> a; rewrite addrC.
  exact: real_norm_metric_translate_continuous.
have htarget a (ha : A a) : closure A (a+y) := hfirst a ha y hy.
exact (@continuous_closed_target_extension
  [the topologicalType of real_norm_metric_space hN]
  [the topologicalType of real_norm_metric_space hN]
  (fun a => a+y) A (closure A) hc (@closed_closure [the topologicalType of real_norm_metric_space hN] A) htarget x hx).
Qed.

(** Source for [norm_closure_rational_scale_stable]: supporting scalar
    closure: stability under rational multiplication becomes stability under
    all real scalars after closure, for Federer 2.3.8, p. 78 *)
Lemma norm_closure_rational_scale_stable (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (A : set (real_norm_metric_space hN)) :
  (forall (q : rat) x, A x -> A ((ratr q : R) *: x)) ->
  forall (c : R) x, closure A x -> closure A (c *: x).
Proof.
move=> hq c x hx.
have hrat q : closure A ((ratr q : R) *: x).
  apply: (@continuous_closed_target_extension
    [the topologicalType of real_norm_metric_space hN]
    [the topologicalType of real_norm_metric_space hN] (fun y => (ratr q : R) *: y)
    A (closure A) _ (@closed_closure [the topologicalType of real_norm_metric_space hN] A) _ x hx).
  - exact: real_norm_metric_scale_continuous.
  - move=> y hy; apply: subset_closure; exact: hq.
pose F : set (real_line_metric R) := [set a | closure A (a *: x)].
have hF : closed F.
  apply: (@preimage_closed (real_line_metric R) (real_norm_metric_space hN)
    (fun a => a *: x) (closure A)); last exact: closed_closure.
  move=> a _; exact: real_norm_metric_scalar_orbit_continuous.
have hsubset : ((fun q : rat => (ratr q : real_line_metric R)) @` setT) `<=` F.
  by move=> a [q _ <-]; exact: hrat.
have hd : dense ((fun q : rat => (ratr q : real_line_metric R)) @` setT).
  exact: dense_rat.
exact (@dense_closed_superset_all (real_line_metric R)
  ((fun q : rat => (ratr q : real_line_metric R)) @` setT) F hd hF hsubset c).
Qed.
