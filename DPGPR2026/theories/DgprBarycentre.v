(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:barycentre: if Z is a finite dimensional normed space, K is a
    compact convex subset of Z, nu is a measure over a set Omega with
    0 < nu(Omega) < infinity, and f : Omega -> K is nu measurable, then
    the integral of f with respect to nu exists (Federer 2.4.12) and
    nu(Omega)^-1 (integral of f) belongs to K (Federer 2.4.19). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP MetricSubsetBackground
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureRestriction
  MeasurableFunctionUP MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegral
  InnerConvex LinearBasis FiniteNormMetricPolish BoundedRestrictedVectorIntegrability
  ClosedConvexIntegralMean RealMetricBackground MetricClosedBalls CompactSetDistanceProfile
  CompactMetricBounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Barycentre.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable d : nat.
Variable e : 'I_d -> V.
Hypothesis he : is_basis e.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Variable m : R.
Variable K : set (real_norm_metric_space hN).
Variable f : X -> real_norm_metric_space hN.

(** Source for [dgpr_barycentre]: blueprint lem:barycentre, the
    membership assertion; Federer 2.4.19, p. 91, applied to the closed
    convex set K. Here m = nu(Omega) and y is the integral of f in the
    sense of Federer 2.4.12. *)
Theorem dgpr_barycentre (y : V) :
  mu setT = m%:E -> 0 < m -> compact K -> is_inner_convex K -> (forall x, K (f x)) ->
  is_measure_vector_integral mu (partial_function_total f) y -> K (m^-1 *: y).
Proof.
move=> hmass hm0 hK hconv hfK hy.
have [x _] : exists x : X, True.
  case: (pselect (exists x : X, True)) => // hn; exfalso.
  have h0 : [set: X] = set0 by apply/seteqP; split=> [z _|z []]; apply: hn; exists z.
  move: hmass; rewrite h0 (measure_empty hm) => -[h].
  by move: hm0; rewrite -h ltxx.
pose c : metric_subset K := exist _ (f x) (mem_set (hfK x)).
have hY := finite_norm_metric_complete (hN := hN) he.
have hKc : closed K := compact_closed (@metric_hausdorff R (real_norm_metric_space hN)) hK.
exact: (@closed_convex_integral_mean R X V N hN hY mu hm m K c f y hmass hm0 hKc hconv hfK hy).
Qed.

(** Source for [dgpr_barycentre_integrable]: blueprint proof of
    lem:barycentre, first sentence: f is bounded, hence summable with
    respect to nu (Federer 2.4.12, pp. 87-88), because V is finite
    dimensional and nu(Omega) is finite. *)
Lemma dgpr_barycentre_integrable :
  mu setT = m%:E -> compact K -> (forall x, K (f x)) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_lp_function mu 1 (partial_function_total f).
Proof.
move=> hmass hK hfK hf.
have [D [hDc hDd]] := finite_norm_metric_separable hN he.
have [L hL] : exists L : R, forall x, N (f x) <= L.
  have [hne|h0] := pselect (K !=set0); last first.
    by exists 0 => x; exfalso; apply: h0; exists (f x); exact: hfK.
  pose C : compact_metric_set (real_norm_metric_space hN) := exist _ K (mem_set (conj hK hne)).
  have [r [_ hr]] := compact_metric_set_ball_bound C (0 : real_norm_metric_space hN).
  exists r => x; have := hr (f x) (hfK x); rewrite /metric_closed_ball /=.
  by rewrite real_norm_metric_distanceE sub0r (real_seminorm_negate hN.1).
have hrestr : measure_restrict mu setT = mu.
  by apply: funext => A; rewrite /measure_restrict setTI.
have := @bounded_restricted_vector_lone R X V N hN D mu hm setT m L f hDc hDd hmass hf hL.
by rewrite hrestr.
Qed.

(** Source for [dgpr_barycentre_exists]: blueprint lem:barycentre: the
    integral y of f exists (Federer 2.4.12) and nu(Omega)^-1 y belongs
    to K (Federer 2.4.19). *)
Theorem dgpr_barycentre_exists :
  mu setT = m%:E -> 0 < m -> compact K -> is_inner_convex K -> (forall x, K (f x)) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  exists y : V, is_measure_vector_integral mu (partial_function_total f) y /\ K (m^-1 *: y).
Proof.
move=> hmass hm0 hK hconv hfK hf.
have hY := finite_norm_metric_complete (hN := hN) he.
have hl := dgpr_barycentre_integrable hmass hK hfK hf.
pose y := @measure_vector_integral R X V N hN hY mu hm (partial_function_total f) hl.
have hy : is_measure_vector_integral mu (partial_function_total f) y.
  exact: measure_vector_integral_specification.
by exists y; split=> //; exact: dgpr_barycentre hmass hm0 hK hconv hfK hy.
Qed.
End Barycentre.
