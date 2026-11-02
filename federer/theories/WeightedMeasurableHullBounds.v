(** Federer (1969), 2.10.24, pp. 187–188: supporting measurable-hull form of
    the B_j/Fatou argument for the Hausdorff application. Cover generators
    can be replaced in the integral comparison by measurable supersets with
    the same small-generator bounds. The weighted covering coefficients stay
    on the original index set, so repeated hulls need not be merged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralBounds MetricDiameter CaratheodoryLimitUP NonnegativeSum
  WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedUpperIntegralBound WeightedBorelFatouBound ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_uniform_measurable_hull_restrictions]: supporting
    precise inputs to the B_j/Fatou comparison of
    2.10.24(1), p. 187, for the closure-based
    Hausdorff application on p. 188. These are
    proved-input laws, not global axioms or a claim
    that arbitrary generating families satisfy them. *)
Definition has_uniform_measurable_hull_restrictions (R : realType) (X : metricType R) (J : choiceType)
    (psi : set X -> \bar R) (S T : J -> set X) (c : J -> \bar R) (f : X -> \bar R) :=
  forall t : R, (1<t)%R -> exists (B : nat -> set X) (r : nat -> R),
    (forall n m, (n<=m)%N -> B n `<=` B m) /\
    psi ([set x | 0<f x] `\` \bigcup_n B n)=0 /\
    (forall n, (0<r n)%R) /\
    (forall n j, measure_measurable psi (B n `&` T j)) /\
    forall n j, extended_metric_diameter (S j)<=(r n)%:E -> psi (B n `&` T j)<=t%:E*c j.

(** Source for [weighted_generator_hull_point_bound]: supporting
    domination after replacing each cover member by its
    measurable hull in 2.10.24, pp. 187–188.
    Original indices and weights are preserved exactly. *)
Lemma weighted_generator_hull_point_bound (R : realType) (X J : choiceType)
    (S T : J -> set X) (G : set J) (u : J -> R) x :
  (forall j, S j `<=` T j) -> weighted_generator_sum S G u x<=weighted_generator_sum T G u x.
Proof.
move=> hST; apply: nonnegative_sum_subset=> j [hj hx]; split=> //; exact: hST j x hx.
Qed.

(** Source for [weighted_measurable_hull_finite_error_bound]: supporting
    finite-budget Fatou comparison in 2.10.24(1),
    p. 187, allowing measurable hulls of the original
    cover members for the Hausdorff application p. 188. *)
Lemma weighted_measurable_hull_finite_error_bound (R : realType) (X : metricType R) (J : choiceType)
    (psi : set X -> \bar R) (S T : J -> set X) (c : J -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) (M t b : R) :
  is_measure psi -> (forall j, 0<=c j) -> (forall j, S j `<=` T j) -> (forall x, 0<=f x) ->
  is_weighted_metric_limit S c psi L -> has_uniform_measurable_hull_restrictions psi S T c f ->
  L f=M%:E -> (1<t)%R -> (0<b)%R ->
  measure_upper_integral psi (partial_function_total f)<=(t*(M+b))%R%:E.
Proof.
move=> hm hc hST hf hL hrestr hval ht hb.
have [B [r [hBinc [hnull [hrpos [hBS hlocal]]]]]] := hrestr t ht.
have hcover n : exists G u, is_weighted_metric_cover S psi (r n)%:E f G u /\
    weighted_generator_cost c G u<(M+b)%R%:E.
  have hl := @weighted_metric_envelope_specification R X J S c psi (r n)%:E.
  have hd : 0<(r n)%:E by rewrite lte_fin; exact: hrpos.
  have hle := @weighted_metric_limit_upper R X J S c psi L hL f _ _ hd hl.
  rewrite hval in hle.
  have hlt : M%:E<(M+b)%R%:E by rewrite lte_fin; lra.
  exact: weighted_metric_envelope_approximation hl (le_lt_trans hle hlt).
pose G n := projT1 (cid (hcover n)).
pose u n := projT1 (cid (projT2 (cid (hcover n)))).
have hGu n := projT2 (cid (projT2 (cid (hcover n)))).
have hdom n : measure_almost_everywhere psi [set x | f x<=weighted_generator_sum T (G n) (u n) x].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (weighted_metric_cover_dominates (hGu n).1))=> x hx.
  exact: le_trans hx (weighted_generator_hull_point_bound (G n) (u n) x hST).
have hbound n j (hj : G n j) : psi (B n `&` T j)<=t%:E*c j.
  apply: hlocal; exact: (@weighted_metric_cover_diameter R X J S psi (r n)%:E f (G n) (u n) (hGu n).1 j hj).
have hh := @weighted_borel_cover_fatou_bound R X J psi T c f B G u t (M+b)%R%:E hm hf
  (ltW (lt_trans (@ltr01 R) ht)) hc hBinc hnull
  (fun n=>weighted_metric_cover_countable (hGu n).1)
  (fun n=>weighted_metric_cover_nonnegative (hGu n).1) hdom (fun n j _=>hBS n j) hbound
  (fun n=>ltW (hGu n).2).
by rewrite -EFinM in hh.
Qed.

(** Source for [weighted_measurable_hull_integral_equality]: supporting
    equality from the precise measurable restriction laws
    used in 2.10.24, pp. 187–188. An actual
    Caratheodory final measure supplies the opposite general
    inequality; no measurability of the original S_j
    or of f is assumed. The restriction laws must
    be proved separately in each application. *)
Theorem weighted_measurable_hull_integral_equality (R : realType) (X : metricType R) (J : choiceType)
    (psi : set X -> \bar R) (S T : J -> set X) (c : J -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) :
  is_measure psi -> (forall j, 0<=c j) -> (forall j, S j `<=` T j) -> (forall x, 0<=f x) ->
  is_caratheodory_limit S c psi -> is_weighted_metric_limit S c psi L ->
  has_uniform_measurable_hull_restrictions psi S T c f ->
  L f=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hm hc hST hf hp hL hrestr.
have hupper := @weighted_metric_limit_upper_integral_bound R X J S c psi L f hp hc hL hf.
apply/eqP; rewrite eq_le hupper /=.
have hnon := weighted_metric_limit_nonnegative hL f.
case hval : (L f)=> [M| |] in hnon *; [|exact: leey|by []].
have hM : (0<=M)%R by move: hnon; rewrite lee_fin.
have hfactor t (ht : (1<t)%R) : measure_upper_integral psi (partial_function_total f)<=(t*M)%R%:E.
  apply: (@extended_upper_bound_from_scaled_errors R _ (t*M)%R t (ltW (lt_trans (@ltr01 R) ht)))=> b hb.
  have hh := @weighted_measurable_hull_finite_error_bound R X J psi S T c L f M t b hm hc hST hf hL hrestr hval ht hb.
  by rewrite mulrDr in hh.
apply: (@extended_upper_bound_from_scaled_errors R _ M M hM)=> e he.
have ht : (1<1+e)%R by lra.
have hh := hfactor (1+e)%R ht; by rewrite mulrDl mul1r [(e*M)%R]mulrC in hh.
Qed.
