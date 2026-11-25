(** Federer (1969), 2.10.24(1), p. 187: the displayed Fatou comparison for
    h_j, expanded using the project's partial-function limits and integrals.
    The B_j are increasing and cover the positive support almost everywhere;
    f need not be measurable. Source context: WeightedMetricEnvelopeUP.v. it
    does not state this weighted-cover theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitExtremaUP PartialFunctionLowerLimitSealed PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureUpperIntegralMonotone MeasureFatou ExtendedLowerLimitUP ExtendedLowerLimit
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale WeightedMetricEnvelopeUP WeightedGeneratorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_borel_cover_fatou_bound]: supporting
    upper-integral comparison in 2.10.24(1), p. 187.
    A fixed factor t and uniform weighted cost C
    suffice; the final theorem subsequently lets the
    excess factor and covering error tend to zero.
    Infinite integral values and zero costs are preserved. *)
Theorem weighted_borel_cover_fatou_bound (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (S : J -> set X) (c : J -> \bar R)
    (f : X -> \bar R) (B : nat -> set X) (G : nat -> set J) (u : nat -> J -> R)
    (t : R) (C : \bar R) :
  is_measure mu -> (forall x, 0<=f x) -> (0<=t)%R -> (forall j, 0<=c j) ->
  (forall n m, (n<=m)%N -> B n `<=` B m) ->
  mu ([set x | 0<f x] `\` \bigcup_n B n)=0 ->
  (forall n, countable (G n)) -> (forall n j, G n j -> (0<=u n j)%R) ->
  (forall n, measure_almost_everywhere mu [set x | f x<=weighted_generator_sum S (G n) (u n) x]) ->
  (forall n j, G n j -> measure_measurable mu (B n `&` S j)) ->
  (forall n j, G n j -> mu (B n `&` S j)<=t%:E*c j) ->
  (forall n, weighted_generator_cost c (G n) (u n)<=C) ->
  measure_upper_integral mu (partial_function_total f)<=t%:E*C.
Proof.
move=> hm hf ht hc hinc hnull hG hu hdom hmeas hlocal hcost.
pose h n := weighted_generator_restriction S (G n) (u n) (B n).
pose a n := nonnegative_sum (G n) (fun j=>(u n j)%:E*mu (B n `&` S j)).
have hi n : is_measure_integral mu (partial_function_total (h n)) (a n) :=
  @weighted_generator_restriction_integral R X J mu S (G n) (u n) (B n) hm (hG n) (hu n) (hmeas n).
have hp n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total (h n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (h n x); split=> //; exact: weighted_generator_restriction_nonnegative.
pose g := @PartialFunctionLowerLimit.value R X (fun n=>partial_function_total (h n)).
have hg := @PartialFunctionLowerLimit.laws R X (fun n=>partial_function_total (h n)).
have hgi := (@measure_fatou R X mu hm (fun n=>partial_function_total (h n)) g hg
  (fun n=>(hi n).1) hp).1.
have hfatou := @measure_fatou_integral_values R X mu hm (fun n=>partial_function_total (h n)) g a
  (measure_lower_integral mu g) hg hp hi hgi.
have hcommon := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT _
  (countableP _) (fun n _=>hdom n).
have hgood : measure_almost_everywhere mu (~` ([set x | 0<f x] `\` \bigcup_n B n)).
  by rewrite /measure_almost_everywhere setCK.
have hfg : measure_almost_everywhere mu (partial_extended_le_locus (partial_function_total f) g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hcommon hgood))=> x [hx hgoodx].
  have hdg : partial_function_domain g x.
    rewrite (partial_function_lower_limit_domain hg); exists 0%N=> n _; by exists (h n x).
  have [z hz] := hdg; exists (f x),z; split=> //; split=> //.
  apply: (partial_function_lower_limit_upper hg hz).
  have [hzero|hzero] := eqVneq (f x) 0.
  - exists 0%N=> n _ y <-; rewrite hzero; exact: weighted_generator_restriction_nonnegative.
  - have hpos : 0<f x by rewrite lt_neqAle eq_sym hzero (hf x).
    have [N _ hxB] : (\bigcup_n B n) x.
      apply: contrapT=> hxB; apply: hgoodx; by split.
    exists N=> n hn y <-; rewrite /h /weighted_generator_restriction (mem_set (hinc N n hn x hxB)).
    exact: hx n Logic.I.
have hupper := @measure_upper_integral_monotone R X mu hm (partial_function_total f) g hfg.
have heq := @measure_upper_integral_unique R X mu g _ _ (measure_upper_integral_specification mu g) hgi.2.1.
rewrite heq in hupper; apply: le_trans hupper (le_trans hfatou _).
have ha n : a n<=t%:E*C.
  apply: le_trans _ (lee_wpmul2l _ (hcost n)); last by rewrite lee_fin.
  rewrite /a /weighted_generator_cost -nonnegative_sum_scale //.
  - apply: nonnegative_sum_mono=> j hj; rewrite muleA [t%:E*(u n j)%:E]muleC -muleA.
    apply: lee_wpmul2l; first by rewrite lee_fin; exact: hu.
    exact: hlocal.
  - move=> j hj; apply: mule_ge0; [by rewrite lee_fin; exact: hu|exact: hc].
apply: (extended_real_supremum_least (extended_lower_limit_laws a))=> b [N hN].
exact: le_trans (hN N (leqnn N)) (ha N).
Qed.
