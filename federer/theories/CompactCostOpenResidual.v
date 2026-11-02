(** Federer (1969), 2.10.22, p. 185: estimate the part of the increasing
    union outside open neighbourhoods of all limiting cover positions. The
    printed estimate psi(residual)<=s-t is expressed here with each finite
    prefix cost added on the left. This equivalent intermediate form avoids
    subtracting an infinite sum. Regularity is used for arbitrary targets,
    exactly as in the printed proof. Source context:
    CompactGeneratorCostUP.v; compact extraction: CompactArrayCluster.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactGeneratorCostUP MaskedCompactGenerators ArrayClusterCost MetricScaleOptionalCover
  MetricScaleMaskedCover MetricDiameter MetricScaleEnvelopeUP CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryLimitAddBounds CaratheodoryBorelRegular
  MeasureUP MeasureBasic RegularMeasureUP RegularMeasureContinuity NonnegativeSum
  SummableCostEnumerationUP ExtendedFiniteIncreasingBounds ExtendedScaledErrorBound RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_open_residual_bound]: supporting
    open-neighbourhood residual estimate in 2.10.22,
    p. 185. The finite prefix may be empty;
    no measurability of the increasing sets is required. *)
Theorem compact_cost_open_residual_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (mu : set X -> \bar R) (A : nat -> set X)
    (d : compact_metric_set X) (u : nat -> nat -> option (compact_metric_set X))
    (v : nat -> bool*compact_hausdorff_space X) (s : R) (err : nat -> R) :
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) mu ->
  is_regular_measure mu ->
  (forall i j, (i<=j)%N -> A i `<=` A j) ->
  (forall j, A j `<=` \bigcup_k optional_generator_set (fun C=>val C) (u j k)) ->
  is_countable_array_cluster (fun j k=>optional_compact_point d (u j k)) v ->
  (forall j, (nonnegative_sum setT (fun k=>(optional_generator_cost c (u j k))%:E)<=(s+err j)%:E)%E) ->
  (forall e : R, 0<e -> exists N, forall j, (N<=j)%N -> err j<=e) ->
  (forall e : R, 0<e -> exists N, forall j k C, (N<=k)%N -> u j k=Some C -> compact_metric_diameter C<e) ->
  forall (V : nat -> set X) (D : {fset nat}),
  (forall k, open (V k)) -> (forall k, masked_compact_set (v k) `<=` V k) ->
  (mu ((\bigcup_j A j) `\` \bigcup_k V k)+(\sum_(k <- D) masked_compact_cost c (v k))%:E<=s%:E)%E.
Proof.
move=> hmu hreg hinc hcover hcluster hbudget herr hsmall V D hV hVV.
pose P := [the topologicalType of (bool*compact_hausdorff_space X)%type].
pose q j k := optional_compact_point d (u j k).
pose w : P -> R := masked_compact_cost c.
pose p := \sum_(k <- D) w (v k).
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := caratheodory_limit_is_measure hmu hc0.
have hw0 z : 0<=w z.
  rewrite /w /masked_compact_cost; case: z.1=> //; exact: compact_cost_nonnegative_law hc z.2.
have hp0 : (0<=p%:E)%E.
  rewrite lee_fin /p big_seq; apply: sumr_ge0=> k hk; exact: hw0.
have hw : continuous (fun z : P => (w z : real_line_metric R)) :=
  masked_compact_cost_continuous (compact_cost_continuous_law hc).
have hbud j : (nonnegative_sum setT (fun k=>(w (q j k))%:E)<=(s+err j)%:E)%E.
  have heq : (fun k=>(w (q j k))%:E)=(fun k=>(optional_generator_cost c (u j k))%:E).
    apply: funext=> k; by rewrite /w /q optional_compact_costE.
  by rewrite heq.
pose T i := A i `\` \bigcup_k V k.
have hrow i : (mu (T i)+p%:E<=s%:E)%E.
  apply: (@caratheodory_limit_add_bound R X (compact_metric_set X) (fun C=>val C)
    (fun C=>(c C)%:E) mu (T i) p%:E s%:E hmu hp0)=> eta xi heta hxi.
  have [b hb] := reciprocal_metric_cutoffs_cofinal heta.
  pose t := (b.+1%:R : R)^-1.
  have ht : 0<t by rewrite /t invr_gt0 ltr0n.
  have [L hL] := hsmall t ht.
  pose F : {fset nat} := seq_fset tt (iota 0 L).
  have hF k : (k \in F)=(k<L)%N by rewrite /F seq_fsetE mem_iota add0n leq0n.
  pose E := fsetU F D.
  pose W k : set P := [set z | masked_compact_set z `<=` V k].
  have hW k : k \in E -> nbhs (v k) (W k).
    move=> hk; exact: masked_compact_open_neighborhood (hV k) (hVV k).
  have hsize : (0<=(size D)%:R+1 :> R) by rewrite addr_ge0 ?ler0n //.
  apply: (@extended_upper_bound_from_scaled_errors R (xi (T i)+p%:E)%E s ((size D)%:R+1) hsize)=> e he.
  have [j [hij [hjW hjcost]]] := @array_cluster_remaining_cost_bound R P w q v s err
    hw hcluster (fun j k=>hw0 (q j k)) hbud herr i D E W e hW he.
  pose J : set nat := setT `\` [set` E].
  have hadmiss k : J k -> (q j k).1 -> (extended_metric_diameter (val (q j k).2)<=eta)%E.
    move=> [_ hkE]; rewrite /q /optional_compact_point; case hu: (u j k)=> [C|] // _.
    have hLk : (L<=k)%N.
      rewrite leqNgt; apply/negP=> hkL; apply: hkE.
      change (is_true (k \in E)); by rewrite /E in_fsetU hF hkL.
    have hdiam := hL j k C hLk hu.
    rewrite compact_metric_diameter_finite_value.
    apply: le_trans _ hb; rewrite lee_fin; exact: ltW hdiam.
  have hcov : T i `<=` \bigcup_(k in J) masked_compact_set (q j k).
    move=> x [hx hxV]; have [k hkT hxk] := hcover j x (hinc i j hij x hx).
    have hqk : masked_compact_set (q j k) x by rewrite /q optional_compact_setE.
    have hkE : ~ (k \in E).
      move=> hkE; apply: hxV; exists k=> //; exact: hjW k hkE x hqk.
    exists k=> //; split=> //; exact hkE.
  have hcost := @metric_scale_masked_cover_bound R X [the choiceType of (nat : Type)] c eta xi (q j) J (T i)
    hxi (compact_cost_nonnegative_law hc) (sub_countable (subset_card_le (fun k (_ : J k)=>Logic.I)) (countableP _))
    hadmiss hcov.
  have hsub : J `<=` setT `\` [set` D].
    move=> k [hk hkE]; split=> // hkD; apply: hkE.
    change (is_true (k \in E)); rewrite /E in_fsetU; apply/orP; right; exact hkD.
  have htail := nonnegative_sum_subset (fun k=>(w (q j k))%:E) hsub.
  have hfinal : (xi (T i)+p%:E<=(s+(size D)%:R*e+e)%:E)%E.
    apply: le_trans (leeD (le_trans hcost htail) (lexx p%:E)) _.
    by rewrite addeC; exact hjcost.
  rewrite mulrDl mul1r addrA; exact hfinal.
have hTi i j (hij : (i<=j)%N) : T i `<=` T j by move=> x [hx hxV]; split=> //; exact: hinc i j hij x hx.
have hlim := regular_measure_continuity_below hm hreg hTi.
have hbound := @extended_nonnegative_limit_add_bound R (fun i=>mu (T i)) (mu (\bigcup_i T i)) p%:E s%:E
  (fun i=>measure_nonnegative hm (T i)) hlim.2 hp0 hrow.
have heq : (\bigcup_i T i)=(\bigcup_i A i) `\` \bigcup_k V k.
  apply/seteqP; split.
  - move=> x [i _ [hx hxV]]; split=> //; by exists i.
  - move=> x [[i _ hx] hxV]; exists i=> //; by split.
by rewrite heq in hbound.
Qed.
