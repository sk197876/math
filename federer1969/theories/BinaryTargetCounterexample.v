(** Federer (1969), 2.2.15, p. 71: the real-valued converse fails for
    arbitrary separable metric targets. The two-point subspace {0,1} is a
    concrete counterexample. Connectedness of real intervals, from the
    already used general-topology scalar background normed_module, rules out
    a continuous curve joining the two values. No external
    descriptive-set-theory theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology normed_module.
From Federer Require Import RealMetricBackground MetricSubsetBackground BorelFunctionUP
  BaireFunctions FiniteCurveApproximationUP BaireTargetNecessity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_binary_curve_cannot_cross]: supporting
    connectedness obstruction for the failure assertion in Federer
    2.2.15, p. 71. A continuous real-valued curve
    taking only values zero and one cannot attain both. *)
Lemma continuous_binary_curve_cannot_cross (R : realType)
    (c : real_line_metric R -> real_line_metric R) a b :
  continuous c -> (forall t, c t = 0 \/ c t = 1) -> c a = 0 -> c b = 1 -> False.
Proof.
move=> hc hr ha hb.
have hwhole : connected (@setT R^o).
  apply/(proj2 (connected_intervalP _)); by move=> x y hx hy z hz.
have hcon : connected (c @` setT).
  apply: connected_continuous_connected hwhole _; exact: continuous_subspaceT hc.
have hint := (proj1 (connected_intervalP _)) hcon.
have h0 : (c @` setT) 0 by exists a.
have h1 : (c @` setT) 1 by exists b.
have hh0 : (0 : R) < 1 / 2 by rewrite divr_gt0 // ltr0n.
have hh1 : (1 / 2 : R) < 1 by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
have hhalf : (0 : R) <= (1/2 : R) <= (1 : R).
  by rewrite (ltW hh0) (ltW hh1).
have [t _ ht] := hint 0 1 h0 h1 (1/2) hhalf.
have [hz|ho] := hr t.
- by move: hh0; rewrite -ht hz ltxx.
- by move: hh1; rewrite -ht ho ltxx.
Qed.

(** Source for [binary_target_has_no_curve_approximation]: concrete
    counterexample to unrestricted metric targets in Federer
    2.2.15, p. 71. A curve within one half
    of both points of {0,1} would have to attain both points. *)
Lemma binary_target_has_no_curve_approximation (R : realType) :
  ~ has_finite_curve_approximation
    [the metricType R of metric_subset ([set 0; 1] : set (real_line_metric R))].
Proof.
pose Y := [the metricType R of metric_subset ([set 0; 1] : set (real_line_metric R))].
have h0 : ([set 0; 1] : set (real_line_metric R)) 0 by left.
have h1 : ([set 0; 1] : set (real_line_metric R)) 1 by right.
pose z0 : Y := Sub 0 (mem_set h0).
pose z1 : Y := Sub 1 (mem_set h1).
move=> h.
have he : (0 : R) < 1/2 by rewrite divr_gt0 // ltr0n.
have he1 : (1/2 : R) < 1 by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
have [c [hc happ]] := h [set z0; z1] (finite_set2 z0 z1) (1/2) he.
have [a ha] := happ z0 (or_introl (erefl _)).
have [b hb] := happ z1 (or_intror (erefl _)).
pose d (t : real_line_metric R) : real_line_metric R := val (c t).
have hd : continuous d.
  move=> t; have hi := @metric_subset_inclusion_continuous R
    [the metricType R of real_line_metric R] [set 0; 1] (c t).
  exact: continuous_comp (hc t) hi.
have hr t : d t = 0 \/ d t = 1 := set_valP (c t).
have hda : d a = 0.
  have [hz|ho] := hr a; first exact hz.
  exfalso; have ha0 : mdist z0 (c a) < 1/2 := ha.
  rewrite metric_subset_distanceE real_line_metric_distanceE /= -/(d a) ho sub0r normrN normr1 in ha0.
  by move: (lt_trans ha0 he1); rewrite ltxx.
have hdb : d b = 1.
  have [hz|ho] := hr b; last exact ho.
  exfalso; have hb0 : mdist z1 (c b) < 1/2 := hb.
  rewrite metric_subset_distanceE real_line_metric_distanceE /= -/(d b) hz subr0 normr1 in hb0.
  by move: (lt_trans hb0 he1); rewrite ltxx.
exact: continuous_binary_curve_cannot_cross hd hr hda hdb.
Qed.

(** Source for [separable_target_borel_not_baire]: direct
    failure assertion in Federer 2.2.15, p. 71,
    witnessed by the separable two-point metric target {0,1}.
    Necessity of the finite-curve condition yields a real-domain
    Borel map which is not Baire. *)
Theorem separable_target_borel_not_baire (R : realType) :
  exists Y : metricType R,
    (exists D : set Y, countable D /\ dense D) /\
    exists f : real_line_metric R -> Y, is_borel_function f /\ ~ is_baire_function f.
Proof.
pose Y := [the metricType R of metric_subset ([set 0; 1] : set (real_line_metric R))].
have h0 : ([set 0; 1] : set (real_line_metric R)) 0 by left.
have h1 : ([set 0; 1] : set (real_line_metric R)) 1 by right.
pose z0 : Y := Sub 0 (mem_set h0).
pose z1 : Y := Sub 1 (mem_set h1).
have heq : ([set z0; z1] : set Y) = setT.
  apply/seteqP; split; first by move=> z hz.
  move=> z _; have [hz|hz] := set_valP z.
  - left; apply: val_inj; exact hz.
  - right; apply: val_inj; exact hz.
exists Y; split.
- exists setT; split.
  + rewrite -heq; exact: finite_set_countable (finite_set2 z0 z1).
  + move=> U [z hz] hU; exists z; by split.
- case: (pselect (exists f : real_line_metric R -> Y,
    is_borel_function f /\ ~ is_baire_function f))=> h; first exact h.
  exfalso; apply: (@binary_target_has_no_curve_approximation R).
  apply: (@borel_baire_target_necessary R Y z0)=> f hf.
  case: (pselect (is_baire_function f))=> hb; first exact hb.
  exfalso; apply: h; exists f; by split.
Qed.
