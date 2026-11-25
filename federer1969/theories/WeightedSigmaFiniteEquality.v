(** Federer (1969), 2.10.24(1), p. 187: equality of the weighted cutoff
    limit and the upper integral when the positive support is a countable
    union of finite-measure sets and 2.10.18 applies. The proof follows the
    printed Borel-restriction and Fatou argument. We also prove the weak
    enlargement variant, permitting zero costs with the established
    corrected quotient; the literal strict case is a consequence. Source
    editions: WeightedMetricEnvelopeUP.v. neither is cited as the identical
    weighted theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  MeasureIntegralBounds BorelRegularMeasureUP TopologicalBorel MetricDiameter
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryBorelRegular CaratheodoryWeakEnlargementUP
  CaratheodoryUniformBorelApproximation BorelFiniteIncreasingCover WeightedBorelFatouBound
  WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedUpperIntegralBound ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_sigma_finite_finite_error_bound]:
    supporting finite-cost estimate in the displayed Fatou
    argument of 2.10.24(1), p. 187. A fixed
    factor t>1 and positive covering error b suffice;
    taking each to its limiting value is done separately. *)
Lemma weighted_sigma_finite_finite_error_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R) (E : set X -> set X) (k : R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R)
    (A : nat -> set X) (M t b : R) :
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  is_weighted_metric_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi L ->
  (forall S, F S -> closed S) -> (forall x, 0<=f x) ->
  (forall n, psi (A n)< +oo) -> [set x | 0<f x] `<=` \bigcup_n A n ->
  L f=M%:E -> (1<t)%R -> (0<b)%R ->
  measure_upper_integral psi (partial_function_total f)<=(t*(M+b))%R%:E.
Proof.
move=> hE hp hL hclosed hf hAfin hsupport hval ht hb.
pose J := [the choiceType of set_type F].
have hc S (hS : F S) := weak_enlargement_cost_nonnegative hE hS.
have hm := caratheodory_limit_is_measure hp (fun j=>hc _ (set_valP j)).
have hr := caratheodory_limit_borel_regular hp (fun j=>hc _ (set_valP j))
  (fun j=>closed_borel_set (hclosed _ (set_valP j))).
have [D [hD [hDfinite [hDinc hAD]]]] := @borel_finite_increasing_cover R X psi A hm hr hAfin.
have [B [r [hB [hBinc [hBD [hnull [hrpos hlocal]]]]]]] :=
  @caratheodory_increasing_borel_generator_bounds R X F c psi E k D (fun _=>t)
    hE hp hclosed hD hDfinite hDinc (fun _=>ht).
have hnullf : psi ([set x | 0<f x] `\` \bigcup_n B n)=0.
  apply: (@measure_null_subset R X psi hm _ _ _ hnull)=> x [hx hxB]; split=> //.
  exact: hAD x (hsupport x hx).
have hcover n : exists G u, is_weighted_metric_cover (fun j : J=>val j) psi (r n)%:E f G u /\
    weighted_generator_cost (fun j : J=>c (val j)) G u<(M+b)%R%:E.
  have hl := @weighted_metric_envelope_specification R X J (fun j=>val j) (fun j=>c (val j)) psi (r n)%:E.
  have hdelta : 0<(r n)%:E by rewrite lte_fin; exact: hrpos.
  have hle := @weighted_metric_limit_upper R X J (fun j=>val j) (fun j=>c (val j)) psi L hL f _ _ hdelta hl.
  rewrite hval in hle.
  have hlt : M%:E<(M+b)%R%:E by rewrite lte_fin; lra.
  exact: weighted_metric_envelope_approximation hl (le_lt_trans hle hlt).
pose G n := projT1 (cid (hcover n)).
pose u n := projT1 (cid (projT2 (cid (hcover n)))).
have hGu n := projT2 (cid (projT2 (cid (hcover n)))).
have hBS n (j : J) (hj : G n j) : measure_measurable psi (B n `&` val j).
  apply: (@measure_measurable_intersection R X psi hm).
  - exact: (@borel_regular_borel_measurable R X psi hm hr (B n) (hB n)).
  - exact: (@borel_regular_borel_measurable R X psi hm hr (val j) (closed_borel_set (hclosed _ (set_valP j)))).
have hbound n (j : J) (hj : G n j) : psi (B n `&` val j)<=t%:E*c (val j).
  have hdj := @weighted_metric_cover_diameter R X J (fun j=>val j) psi (r n)%:E f (G n) (u n) (hGu n).1 j hj.
  exact: (hlocal n (val j) (set_valP j) hdj).
have hfatou := @weighted_borel_cover_fatou_bound R X J psi (fun j=>val j) (fun j=>c (val j)) f B G u t (M+b)%R%:E
  hm hf (ltW (lt_trans (@ltr01 R) ht)) (fun j=>hc _ (set_valP j)) hBinc hnullf
  (fun n=>weighted_metric_cover_countable (hGu n).1)
  (fun n=>weighted_metric_cover_nonnegative (hGu n).1)
  (fun n=>weighted_metric_cover_dominates (hGu n).1) hBS hbound (fun n=>ltW (hGu n).2).
by rewrite -EFinM in hfatou.
Qed.

(** Source for [weighted_metric_limit_sigma_finite_equality]:
    2.10.24(1), p. 187, with the proved weak
    enlargement conditions as an additional generalisation.
    Only the positive support is covered by finite-measure
    sets. f may be nonmeasurable or infinite-valued,
    and the resulting upper integral may be infinite. *)
Theorem weighted_metric_limit_sigma_finite_equality (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R) (E : set X -> set X) (k : R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) (A : nat -> set X) :
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  is_weighted_metric_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi L ->
  (forall S, F S -> closed S) -> (forall x, 0<=f x) ->
  (forall n, psi (A n)< +oo) -> [set x | 0<f x] `<=` \bigcup_n A n ->
  L f=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hE hp hL hclosed hf hAfin hsupport.
have hc (j : set_type F) := weak_enlargement_cost_nonnegative hE (set_valP j).
apply/eqP; rewrite eq_le (@weighted_metric_limit_upper_integral_bound R X [the choiceType of set_type F]
  (fun j=>val j) (fun j=>c (val j)) psi L f hp hc hL hf) /=.
have hnon := weighted_metric_limit_nonnegative hL f.
case hval : (L f)=> [M| |] in hnon *; [|exact: leey|by []].
have hM : (0<=M)%R by move: hnon; rewrite lee_fin.
have hfactor (t : R) (ht : (1<t)%R) :
    measure_upper_integral psi (partial_function_total f)<=(t*M)%R%:E.
  apply: (@extended_upper_bound_from_scaled_errors R _ (t*M)%R t (ltW (lt_trans (@ltr01 R) ht)))=> b hb.
  have hh := @weighted_sigma_finite_finite_error_bound R X F c psi E k L f A M t b
    hE hp hL hclosed hf hAfin hsupport hval ht hb.
  by rewrite mulrDr in hh.
apply: (@extended_upper_bound_from_scaled_errors R _ M M hM)=> e he.
have ht : (1<1+e)%R by lra.
have hh := hfactor (1+e)%R ht; by rewrite mulrDl mul1r [(e*M)%R]mulrC in hh.
Qed.
