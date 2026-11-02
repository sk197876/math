(** Supporting Federer (1969), 2.10.13, p. 177: localise the
    finite-variation hypothesis and use the nonexpanding arc-length factor
    of 2.5.16, pp. 109–110. No relevant Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds RealMetricBackground CurveVariationUP CurveArcLength StieltjesSubstitution
  SegmentRetractionTopology MetricCurveAbsoluteContinuityUP OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_chain_sum_reparametrization]: supporting
    reparametrisation of the finite chains of 2.5.16, p. 109,
    for the interval-local reduction in 2.10.13, p. 177. *)
Lemma metric_chain_sum_reparametrization (R : realType) (Y : metricType R)
    (g : R -> Y) (r : R -> R) (s : seq R) :
  chain_sum (g \o r) s=chain_sum g (map r s).
Proof.
have [n] := ubnP (size s); elim: n s=> // n ih [|t [|u rest]] hsize //.
by rewrite !map_cons !chain_sum_cons -map_cons ih //; move: hsize; rewrite /= ltnS.
Qed.

(** Source for [metric_variation_reparametrization_bound]: supporting
    monotone change of parameter in 2.5.16, p. 109, used to
    reduce the finite interval in 2.10.13, p. 177. The target
    is an arbitrary metric space, not only the real line. *)
Lemma metric_variation_reparametrization_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (r : R -> R) (a b : R) :
  (forall x y, x<=y -> r x<=r y) -> a<=b ->
  (curve_variation (g \o r) a b<=curve_variation g (r a) (r b))%E.
Proof.
move=> hr hab; apply: extended_real_sup_least=> z [s [hs ->]].
rewrite metric_chain_sum_reparametrization; apply: extended_real_sup_upper.
by exists (map r s); split; first exact: variation_partition_map hr hs.
Qed.

(** Source for [metric_chain_sum_equal_on]: supporting locality of
    the variation sums in 2.5.16, p. 109, used in 2.10.13,
    p. 177. Only values at the listed parameters matter. *)
Lemma metric_chain_sum_equal_on (R : realType) (Y : metricType R)
    (g h : R -> Y) (s : seq R) :
  (forall x, x \in s -> g x=h x) -> chain_sum g s=chain_sum h s.
Proof.
have [n] := ubnP (size s); elim: n s=> // n ih [|t [|u rest]] hsize // he.
have ht : g t=h t by apply: he; rewrite inE eqxx.
have hu : g u=h u by apply: he; rewrite !inE eqxx orbT.
rewrite !chain_sum_cons ht hu; congr (_+_); apply: ih.
- by move: hsize; rewrite /= ltnS.
move=> x hx.
by apply: he; rewrite inE hx orbT.
Qed.

(** Source for [metric_curve_variation_equal_on]: supporting locality
    of V_a^b g, 2.5.16, p. 109, in 2.10.13, p. 177.
    The equality includes infinite variation and repeated partition terms. *)
Lemma metric_curve_variation_equal_on (R : realType) (Y : metricType R)
    (g h : R -> Y) (a b : R) :
  (forall x, (a<=x<=b)%R -> g x=h x) -> curve_variation g a b=curve_variation h a b.
Proof.
move=> he.
have hsum s (hs : is_variation_partition a b s) : chain_sum g s=chain_sum h s.
  apply: metric_chain_sum_equal_on=> x hx.
  exact: he x (variation_partition_bounds hs hx).
congr (extended_real_sup _); apply/seteqP; split=> z [s [hs ->]];
  exists s; split=> //; by rewrite (hsum s hs).
Qed.

(** Source for [metric_finite_interval_retracted_variation]: supporting
    localisation of the sole finite-variation interval in 2.10.13,
    p. 177. The segment retraction is a proof representative;
    no finite variation outside [a,b] is imposed on the given curve. *)
Lemma metric_finite_interval_retracted_variation (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : a<=b -> (curve_variation g a b < +oo)%E ->
  curve_locally_finite_variation (g \o @segment_retraction R a b).
Proof.
move=> hab hV u v huv.
have hr := @segment_retraction_monotone R a b.
apply: le_lt_trans (@metric_variation_reparametrization_bound R Y g _ u v hr huv) _.
apply: le_lt_trans _ hV; apply: curve_variation_monotone.
- by have /andP[] := segment_retraction_bounds u hab.
- exact: hr.
- by have /andP[_] := segment_retraction_bounds v hab.
Qed.

(** Source for [metric_retracted_curve_continuous]: supporting
    continuous representative in 2.10.13, p. 177. Composition
    with the existing continuous segment retraction preserves
    the given global continuity and fixes both endpoints. *)
Lemma metric_retracted_curve_continuous (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) :
  continuous (g : real_line_metric R -> Y) ->
  continuous (g \o @segment_retraction R a b : real_line_metric R -> Y).
Proof.
move=> hg x; apply: continuous_comp (hg _).
exact: segment_retraction_continuous.
Qed.

(** Source for [metric_absolute_continuity_equal_on]: supporting
    locality of absolute continuity on [a,b] in 2.10.13, p. 177,
    using the finite-family definition in 2.9.20(3), p. 165,
    extended to metric targets in 2.9.22, p. 167. *)
Lemma metric_absolute_continuity_equal_on (R : realType) (Y : metricType R)
    (g h : R -> Y) (a b : R) :
  (forall x, (a<=x<=b)%R -> g x=h x) ->
  (is_absolutely_continuous_metric_curve g a b <-> is_absolutely_continuous_metric_curve h a b).
Proof.
move=> he.
have hsum s : is_ordered_real_interval_family a b s ->
    metric_interval_family_increment_sum g s=metric_interval_family_increment_sum h s.
  move=> hs; rewrite /metric_interval_family_increment_sum !big_seq.
  apply: eq_bigr=> [[u v] huv].
  have [hau [huv' hvb]] := ordered_real_interval_family_cell_bounds hs huv.
  rewrite (he u ltac:(by rewrite hau (le_trans (ltW huv') hvb)))
    (he v ltac:(by rewrite (le_trans hau (ltW huv')) hvb)).
  by [].
split=> hAC e heps; have [d [hd hb]] := hAC e heps; exists d; split=> // s hs hlen.
- by rewrite -(hsum s hs); exact: hb s hs hlen.
- by rewrite (hsum s hs); exact: hb s hs hlen.
Qed.
