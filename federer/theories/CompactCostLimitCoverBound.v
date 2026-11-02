(** Federer (1969), 2.10.22, pp. 185–186:
    finish the compact-cover limit estimate. A finite
    prefix, an arbitrarily cheap interior-containing tail,
    and the mixed residual cover B. Keeping the
    prefix cost on the left gives nu_delta(B)<=s
    without subtraction of extended values. This is the
    printed final argument in finite-prefix form. Source
    editions: CompactGeneratorCostUP.v; open tail choices:
    CompactCostTailRefinement.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactGeneratorCostUP CompactCostTailRefinement CompactCostMixedResidual MaskedCompactGenerators
  MetricScaleMaskedCover MetricDiameter MetricScaleEnvelopeUP MetricScaleCutoffCost CaratheodoryLimitUP
  MeasureUP MeasureBasic MeasureSplit RegularMeasureUP NonnegativeSum NonnegativeSeriesTails
  ExtendedScaledErrorBound LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_limit_cover_bound]: supporting
    final bounded-target estimate in 2.10.22,
    p. 186. Finite covers, zero costs and
    an empty target are retained through the activity flags. *)
Theorem compact_cost_limit_cover_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta s : R) (nu mu : set X -> \bar R) (B : set X)
    (K : set (compact_hausdorff_space X)) (v : nat -> bool*compact_hausdorff_space X) :
  metric_boundedly_compact X -> 0<delta ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) mu ->
  is_measure mu -> is_regular_measure mu -> compact K -> (forall k, K (v k).2) ->
  (forall k, (v k).1 -> compact_metric_diameter (v k).2<=delta) ->
  (nonnegative_sum setT (fun k=>(masked_compact_cost c (v k))%:E)< +oo)%E ->
  (forall (V : nat -> set X) (D : {fset nat}), (forall k, open (V k)) ->
    (forall k, masked_compact_set (v k) `<=` V k) ->
    (mu (B `\` \bigcup_k V k)+(\sum_(k <- D) masked_compact_cost c (v k))%:E<=s%:E)%E) ->
  (nu B<=s%:E)%E.
Proof.
move=> hX hd hn hmu hm hr hK hv hdiam hfinite hres.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hnu := metric_scale_envelope_is_measure hn hc0.
have h0 k : (0<=(masked_compact_cost c (v k))%:E)%E.
  rewrite lee_fin /masked_compact_cost; case: (v k).1=> //; exact: compact_cost_nonnegative_law hc (v k).2.
apply: (@extended_upper_bound_from_scaled_errors R (nu B) s 2 _); first by rewrite ler0n.
move=> e he.
have [N1 hN1] := compact_masked_series_small_diameter hc hK hv hfinite hd.
have [N2 hN2] := nonnegative_series_tail_small h0 hfinite he.
pose N := maxn N1 N2.
pose D : {fset nat} := seq_fset tt (iota 0 N).
have hD k : (k \in D)=(k<N)%N by rewrite /D seq_fsetE mem_iota add0n leq0n.
pose J : set nat := ~` [set` D].
have hJ k : J k -> (N<=k)%N.
  move=> hk; rewrite leqNgt; apply/negP=> hkN; apply: hk; change (is_true (k \in D)); by rewrite hD.
have hJmem k : k \notin D -> J k by move=> hk hkD; change (is_true (k \in D)) in hkD; by move: hk; rewrite hkD.
have hdlate k (hk : J k) : (v k).1 -> compact_metric_diameter (v k).2<delta.
  exact: hN1 k (leq_trans (leq_maxl N1 N2) (hJ k hk)).
have [w [hvw [hwd hsumw]]] := @compact_masked_open_tail_refinement R X c hc v J delta e hX he hdlate.
pose C := \bigcup_(k in [set` D]) masked_compact_set (v k).
pose T := \bigcup_(k in J) masked_compact_set (w k).
pose V k := interior (masked_compact_set (w k)).
pose E := B `\` (C `|` \bigcup_(k in J) V k).
pose p := \sum_(k <- D) masked_compact_cost c (v k).
have hp0 : (0<=p%:E)%E by rewrite /p -sumEFin; rewrite big_seq; apply: sume_ge0=> k hk; exact: h0.
have hmixed : (mu E+p%:E<=s%:E)%E.
  apply: (@compact_cost_mixed_residual_bound R X mu B v D p%:E s%:E hm hr hp0).
  - move=> W hW hCW; exact: hres W D hW hCW.
  - by move=> k hk; exact: open_interior.
  - move=> k hk; exact: hvw k (hJmem k hk).
have hcpref : (nu C<=p%:E)%E.
  have hh := @metric_scale_masked_cover_bound R X [the choiceType of (nat : Type)] c delta%:E nu v [set` D] C
    hn (compact_cost_nonnegative_law hc) (finite_set_countable (finite_fset D)).
  have hdc k (hk : [set` D] k) (hactive : (v k).1) : (extended_metric_diameter (val (v k).2)<=delta%:E)%E.
    rewrite compact_metric_diameter_finite_value lee_fin; exact: hdiam k hactive.
  have hbound := hh hdc (fun x hx=>hx).
  rewrite nonnegative_sum_finite in hbound; last by move=> k hk; exact: h0.
  by rewrite sumEFin in hbound.
have hctail : (nu T<=nonnegative_sum J (fun k=>(masked_compact_cost c (w k))%:E))%E.
  apply: (@metric_scale_masked_cover_bound R X [the choiceType of (nat : Type)] c delta%:E nu w J T
    hn (compact_cost_nonnegative_law hc) (sub_countable (subset_card_le (fun k (_ : J k)=>Logic.I)) (countableP _))).
  - move=> k hk hactive; rewrite compact_metric_diameter_finite_value lee_fin; exact: ltW (hwd k hk hactive).
  - by move=> x hx.
have htail : (nu T<=(2*e)%:E)%E.
  have hsub : J `<=` [set k | (N2<=k)%N].
    move=> k hk; exact: leq_trans (leq_maxr N1 N2) (hJ k hk).
  have hs := le_trans (nonnegative_sum_subset (fun k=>(masked_compact_cost c (v k))%:E) hsub) (ltW hN2).
  have hh := le_trans hctail (le_trans hsumw (leeD hs (lexx (e/2)%:E))).
  apply: le_trans hh _; rewrite -EFinD lee_fin; lra.
have hE : (nu E<=mu E)%E.
  apply: (@caratheodory_limit_upper R X (compact_metric_set X) (fun C=>val C) (fun C=>(c C)%:E) mu hmu E delta%:E nu _ hn).
  by rewrite lte_fin.
have hBE : B `<=` (C `|` E) `|` T.
  move=> x hx; case: (pselect (C x))=> hxC; first by left; left.
  case: (pselect (T x))=> hxT; first by right.
  left; right; split=> //; move=> [hxC'|[k hk hxV]]; first exact: hxC hxC'.
  apply: hxT; exists k=> //; exact: interior_subset hxV.
have hCE := @measure_binary_cover R X nu hnu (C `|` E) C E (fun x hx=>hx).
have hB := @measure_binary_cover R X nu hnu B (C `|` E) T hBE.
have hh := le_trans hB (leeD (le_trans hCE (leeD hcpref hE)) htail).
rewrite (addeC p%:E (mu E)) in hh.
have hfinal := le_trans hh (leeD hmixed (lexx (2*e)%:E)).
by rewrite -EFinD in hfinal.
Qed.
