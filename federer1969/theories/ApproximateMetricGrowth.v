(** Federer (1969), 3.1.8, p. 217: the finite
    approximate upper-growth hypothesis and its density consequences.
    The quotient retains its punctured actual domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureSetDensity MeasureDerivationContext
  MeasureApproximateLimitUP MeasureApproximateOrderLimits ApproximateOrderThresholdRays
  LocalZeroDensity MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [partial_metric_growth_quotient]: the quotient
    in the hypothesis of Federer 3.1.8, p. 217,
    written with metric distances. Its value is defined precisely
    at the points of A different from its base point. *)
Definition partial_metric_growth_quotient (R : realType) (X Y : metricType R)
    (A : set X) (f : X->Y) (a : X) : partial_function X (\bar R) :=
  partial_function_source_restrict [set x | A x /\ x!=a]
    (partial_function_total (fun x=>(mdist (f x) (f a)/mdist x a)%:E)).

(** Source for [metric_growth_exception]: the exceptional
    set inside Q(u,r,j) in Federer 3.1.8, p. 217.
    Points outside A remain exceptional, independently of the
    representative's values there. *)
Definition metric_growth_exception (R : realType) (X Y : metricType R)
    (A : set X) (f : X->Y) (a : X) (M : R) : set X :=
  [set x | ~A x \/ M*mdist x a<mdist (f x) (f a)].

(** Source for [finite_approximate_growth_exception]: the first
    density consequence of Federer 3.1.8, p. 217.
    A finite approximate upper limit supplies a positive finite
    coefficient whose exceptional set has density zero. *)
Theorem finite_approximate_growth_exception (R : realType)
    (X Y : metricType R) (phi : set X->\bar R) (V : X->set X->Prop)
    (A : set X) (f : X->Y) a :
  is_measure_derivation_context phi V ->
  (measure_approximate_upper_limit phi V (partial_metric_growth_quotient A f a) a< +oo)%E ->
  exists M : R, 0<M /\
    partial_function_graph
      (measure_set_density phi V (metric_growth_exception A f a M)) a 0%E.
Proof.
move=> hc hg.
have [q [_ hq]] := (approximate_upper_limit_rational_ray hc
  (partial_metric_growth_quotient A f a) a +oo%E).1 hg.
pose M := `|ratr q : R|+1.
have hqM : (ratr q : R)<M.
  apply: le_lt_trans (ler_norm _) _; by rewrite /M ltrDl ltr01.
have hM : 0<M.
  apply: le_lt_trans (normr_ge0 (ratr q : R)) _; by rewrite /M ltrDl ltr01.
exists M; split=> //.
apply: (@local_zero_density_mono R X phi V
  (metric_growth_exception A f a M)
  (~` partial_function_preimage (partial_metric_growth_quotient A f a)
    [set y | (y<=(ratr q : R)%:E)%E]) setT a hc openT I _ hq).
move=> x _ hbad [y [hgraph hy]].
change ((A x /\ x!=a) /\ (mdist (f x) (f a)/mdist x a)%:E=y) in hgraph.
have [[hx hne] hval] := hgraph.
change (is_true (y<=(ratr q : R)%:E)%E) in hy.
rewrite -hval lee_fin in hy.
have hp : 0<mdist x a by rewrite mdist_gt0.
have hbound : mdist (f x) (f a)<=M*mdist x a.
  have hqbound : mdist (f x) (f a)<=(ratr q : R)*mdist x a.
    by move: hy; rewrite ler_pdivrMr.
  apply: (le_trans hqbound _).
  apply: ler_wpM2r; [exact: ltW hp|exact: ltW hqM].
case: hbad=> [hn|hlt]; first exact: hn hx.
by have := lt_le_trans hlt hbound; rewrite ltxx.
Qed.

(** Source for [growth_exception_approximate_continuity]:
    the assertion that f is approximately continuous at every
    point of A in the first proof paragraph of Federer 3.1.8,
    p. 217. This local argument needs no prior measurability. *)
Theorem growth_exception_approximate_continuity (R : realType)
    (X Y : metricType R) (phi : set X->\bar R) (V : X->set X->Prop)
    (A : set X) (f : X->Y) a M :
  is_measure_derivation_context phi V -> A a -> 0<M ->
  partial_function_graph
    (measure_set_density phi V (metric_growth_exception A f a M)) a 0%E ->
  is_measure_approximately_continuous_at phi V
    (partial_function_source_restrict A (partial_function_total f)) a.
Proof.
move=> hc ha hM hzero; exists (f a); split; first by split.
move=> W hW.
have [e he heW] := (metricType_numDomainType.nbhs_mdistP (f a) _).1 hW.
have hd : 0<e/M by rewrite divr_gt0.
apply: (@local_zero_density_mono R X phi V _
  (metric_growth_exception A f a M) [set x | mdist a x<e/M] a hc
  (metric_open_ball_open _ _) _ _ hzero).
- change (is_true (mdist a a<e/M)); by rewrite mdistxx.
- move=> x hx hnot; apply: contrapT=> hgood.
  have hAx : A x by apply: contrapT=> hn; apply: hgood; left.
  have hbound : mdist (f x) (f a)<=M*mdist x a.
    rewrite leNgt; apply/negP=> hbad; apply: hgood; right; exact hbad.
  apply: hnot; exists (f x); split; first by split.
  apply: heW.
  change (is_true (mdist (f a) (f x)<e)); rewrite metric_sym.
  apply: (le_lt_trans hbound _).
  change (is_true (mdist a x<e/M)) in hx.
  move: hx; by rewrite ltr_pdivlMr // (metric_sym a x) mulrC.
Qed.

(** Source for [metric_growth_exception_domain_agreement]:
    the missing-domain alternative in Q(u,r,j), Federer
    3.1.8, p. 217, makes values outside A irrelevant.
    In particular an auxiliary measurable extension may be used
    without changing any exceptional section at a base in A. *)
Lemma metric_growth_exception_domain_agreement (R : realType) (X Y : metricType R)
    (A : set X) (f g : X->Y) a M :
  A a -> (forall x, A x -> f x=g x) ->
  metric_growth_exception A f a M=metric_growth_exception A g a M.
Proof.
move=> ha hfg; apply/seteqP; split=> x hx.
- case: (pselect (A x))=> [hAx|hAx]; last by left.
  case: hx=> [hn|hb]; first by exfalso; exact: hn hAx.
  right; by rewrite -(hfg x hAx) -(hfg a ha).
- case: (pselect (A x))=> [hAx|hAx]; last by left.
  case: hx=> [hn|hb]; first by exfalso; exact: hn hAx.
  right; by rewrite (hfg x hAx) (hfg a ha).
Qed.
