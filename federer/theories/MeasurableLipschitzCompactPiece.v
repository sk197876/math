(** Federer (1969), 3.1.16, p. 228: the compact Lipschitz restriction
    chosen in each finite annulus. Expand the use of 3.1.8 and measurable
    inner approximation into disjoint compact pieces and a finite union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import LipschitzUP LipschitzBasic CompactDisjointLipschitzUnion
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureSequencePrefixes
  MeasureFinitePrefixError BorelRegularMeasureUP BorelRegularApproximation
  GeometricErrorBudget MeasureGeometricCover SetSequenceDisjointification
  MetricClosedBalls TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_lipschitz_compact_piece]: the choice of C_i
    in the proof of Federer 3.1.16, p. 228. A measurable finite-measure
    set covered by countably many measurable Lipschitz pieces contains
    a compact Lipschitz restriction with arbitrarily small measure loss,
    when it lies in a compact set. *)
Theorem measurable_lipschitz_compact_piece (R : realType) (X Y : metricType R)
    (mu : set X->\bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (A K : set X) (E : nat->set X) (f : X->Y) (e : R) :
  compact K -> A `<=` K -> measure_measurable mu A -> (mu A< +oo)%E ->
  (forall i, measure_measurable mu (E i) /\ is_metric_lipschitz (E i) f) ->
  A `<=` \bigcup_i E i -> 0<e ->
  exists C, compact C /\ C `<=` A /\ is_metric_lipschitz C f /\ (mu (A `\` C)<e%:E)%E.
Proof.
move=>hK hAK hA hfin hE hcover he.
pose D i := A `&` set_sequence_disjointify E i.
have hDm i : measure_measurable mu (D i).
  rewrite /D /set_sequence_disjointify.
  apply: (@measure_measurable_intersection R X mu hm _ _ hA).
  apply: (@measure_measurable_difference R X mu hm _ _ (hE i).1).
  exact: (@measure_sequence_prefix_measurable R X mu hm E (fun j=>(hE j).1) i).
have hDA i : D i `<=` A by move=>x [].
have hDf i : (mu (D i)< +oo)%E := le_lt_trans (measure_mono hm (hDA i)) hfin.
have hex i := @borel_regular_closed_approximation R X mu hm hr (D i)
  (hDm i) (hDf i) _ (geometric_error_budget_positive i he).
have [C hC] := choice hex.
have hCc i : compact (C i).
  have hsub : C i `<=` K by move=>x hx; exact (hAK x (hDA i x ((hC i).2.1 x hx))).
  have hid : C i=K `&` C i by apply/seteqP; split=>x; [move=>hx; split=>//; exact: hsub|by move=>[]].
  rewrite hid; exact: compact_closedI hK (hC i).1.
have hCA i : C i `<=` A by move=>x hx; exact (hDA i x ((hC i).2.1 x hx)).
have hCL i : is_metric_lipschitz (C i) f.
  have [L [hL hb]] := (hE i).2.
  exists L; split=>//; apply: (@metric_lipschitz_bound_restrict R X Y (E i) (C i) f L _ hb).
  by move=>x hx; exact ((hC i).2.1 x hx).2.1.
have hdis i j : i!=j -> forall x, C i x -> C j x -> False.
  move=>hne x hxi hxj.
  exact (@set_sequence_disjointify_disjoint X E i j hne x ((hC i).2.1 x hxi).2 ((hC j).2.1 x hxj).2).
have herror : (mu (A `\` \bigcup_i C i)<e%:E)%E.
  apply: (@measure_geometric_cover_bound R X mu hm (A `\` \bigcup_i C i) (fun i=>D i `\` C i) e he _ (fun i=>(hC i).2.2)).2.
  move=>x [hx hn].
  have hDx : (\bigcup_i set_sequence_disjointify E i) x.
    by rewrite set_sequence_disjointify_union; exact: hcover.
  have [i _ hi] := hDx; exists i=>//; split; first by split.
  by move=>hc; apply: hn; exists i.
have [N hN] := @measure_finite_prefix_error R X mu hm A C e%:E hA hfin
  (fun i=>borel_regular_borel_measurable hm hr (closed_borel_set (hC i).1)) herror.
have hprefix n : compact (set_sequence_prefix C n) /\ is_metric_lipschitz (set_sequence_prefix C n) f.
  elim: n=>[|n [hc hl]].
  - rewrite set_sequence_prefix_zero; split; first exact: compact0.
    exact: metric_lipschitz_of_bound (least_metric_lipschitz_bound (@metric_lipschitz_empty R X Y f)).
  - rewrite set_sequence_prefix_succ; split; first exact: compactU hc (hCc n).
    apply: compact_disjoint_lipschitz_union hc (hCc n) _ hl (hCL n).
    move=>x [i hi hxi] hxn.
    have hne : i!=n by rewrite neq_ltn hi.
    exact (@hdis i n hne x hxi hxn).
exists (set_sequence_prefix C N); split; first exact (hprefix N).1.
split; first by move=>x [i _ hx]; exact: hCA i x hx.
by split; [exact (hprefix N).2|exact hN].
Qed.
