(** General topology supporting Federer (1969), 2.8.18, p. 152: every target
    subset of the separable ambient metric space is separable, as required
    in 2.8.15. This proof uses the existing sealed countable open base, and
    supplies witnesses only inside an opaque existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground MetricClosedBalls
  CountableOpenBaseUP SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_separable]: supporting hereditary separability
    used in Federer 2.8.18, p. 152 The subset need not be closed, measurable
    or nonempty. *)
Theorem metric_subset_separable (R : realType) (X : metricType R) (A : set X) :
  (exists D : set X, countable D /\ dense D) ->
  exists H : set (metric_subset A), countable H /\ dense H.
Proof.
move=> [D [hc hd]]; case: (pselect (exists a, A a))=> [[a0 ha0]|hempty].
- pose U := @SeparableMetricBase.value R X D hc hd.
  have hU := @SeparableMetricBase.laws R X D hc hd.
  have hex n : exists a : metric_subset A,
      (exists b, U n b /\ A b) -> U n (val a).
    case: (pselect (exists b, U n b /\ A b))=> [[b [hb ha]]|hn].
    + by exists (@exist X (fun x => x \in A) b (mem_set ha)).
    + exists (@exist X (fun x => x \in A) a0 (mem_set ha0)); by move=> h; exfalso; exact: hn h.
  pose p n := projT1 (cid (hex n)).
  have hp n := projT2 (cid (hex n)).
  exists (p @` setT); split.
  + exact: sub_countable (card_image_le p setT) (countableP setT).
  + move=> W [x hx] ho.
    have hnb : nbhs x W by rewrite openE in ho; exact: ho x hx.
    have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hnb.
    have hball : [set y : X | mdist (val x) y < e] (val x) by rewrite /= mdistxx.
    have [i [hi his]] := @countable_base_refines X U hU _
      (metric_open_ball_open (val x) e) (val x) hball.
    have hmeet : exists b, U i b /\ A b by exists (val x); split=> //; exact: set_valP x.
    exists (p i); split; last by exists i.
    apply: hb; change (mdist (val x) (val (p i)) < e).
    exact: his _ (hp i hmeet).
- exists set0; split; first exact: countable0.
  move=> W [x _] _; exfalso; apply: hempty; exists (val x); exact: set_valP x.
Qed.
