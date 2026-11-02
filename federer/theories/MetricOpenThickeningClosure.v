(** Federer (1969), 3.2.37, p. 274: actual open tubes are unchanged
    by closure. These metric facts include empty sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import MetricOpenThickening MetricClosedBalls
  MetricSetDistanceUP MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_thickening_empty]: supporting the empty
    source case of the definitions in Federer 3.2.37, p. 273. *)
Lemma metric_open_thickening_empty (R:realType) (X:metricType R) (r:R):
  metric_open_thickening (@set0 X) r=set0.
Proof. apply/seteqP; split=>[x [a ha _]|x hx]; by []. Qed.

(** Source for [metric_open_thickening_monotone]: supporting the
    projection and Gross lower bounds in Federer 3.2.37, p. 274. *)
Lemma metric_open_thickening_monotone (R:realType) (X:metricType R)
    (A B:set X) (r:R): A `<=` B ->
  metric_open_thickening A r `<=` metric_open_thickening B r.
Proof. move=>h x [a ha hax]; exists a=>//; exact:h. Qed.

(** Source for [metric_open_thickening_closure]: the actual tube
    identity underlying the closure invariance in Federer 3.2.37,
    p. 274. The metric closure argument requires no nearest points. *)
Lemma metric_open_thickening_closure (R:realType) (X:metricType R)
    (A:set X) (r:R):
  metric_open_thickening (closure A) r=metric_open_thickening A r.
Proof.
apply/seteqP; split; last first.
- apply:metric_open_thickening_monotone=>x hx; exact:subset_closure hx.
- move=>x [a ha hax].
  have he:(0<r-mdist a x)%R by rewrite subr_gt0.
  have hN:nbhs a [set b|mdist a b<r-mdist a x].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    by exists (r-mdist a x).
  have [b [hb hba]]:=ha _ hN; exists b=>//.
  have ht:=metric_triangle b a x.
  rewrite (metric_sym b a) in ht.
  change (is_true (mdist a b<r-mdist a x)) in hba.
  change (is_true (mdist b x<r)); lra.
Qed.

(** Source for [metric_open_thickening_distance]: the open-tube
    notation dist(x,S)<r in Federer 3.2.37, p. 273, agrees with
    the actual union of balls whenever a real-valued distance obeys
    the independent infimum laws. No such object is required for
    the empty source. *)
Lemma metric_open_thickening_distance (R:realType) (X:metricType R)
    (A:set X) (d:X->R) (r:R): is_metric_set_distance A d ->
  metric_open_thickening A r=[set x|d x<r].
Proof.
move=>hd; apply/seteqP; split.
- move=>x [a ha hax]; apply:(le_lt_trans (@metric_set_distance_lower R X A d hd x a ha)).
  by rewrite metric_sym.
- move=>x hx.
  have he:(0<r-d x)%R by rewrite subr_gt0.
  have [a [ha hxa]]:=metric_set_distance_approximation hd x he.
  exists a=>//; change (is_true (mdist a x<r)).
  rewrite metric_sym; move:hxa; by rewrite addrCA subrr addr0.
Qed.
