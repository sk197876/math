(** Federer (1969), 2.4.14, p. 88: zero-norm cases and equality in the
    integral comparison for Holder's inequality. These supporting lemmas
    derive that fact from characteristic lower functions, not an external
    integration theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds CountableOrderIntervals
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralAlmostEquality MeasureDensityNullSets PartialExtendedOrderLoci
  MeasureNonnegativeThresholdBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_integral_zero_superlevel_null]: supporting
    positive-superlevel test for equality in Federer 2.4.14, p. 88 The
    characteristic lower bound forces each positive level set to be null
    when the nonnegative integral is zero. *)
Lemma nonnegative_integral_zero_superlevel_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (c : R) :
  is_measure_integral mu f 0 ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < c)%R ->
  mu (partial_function_preimage f [set y | c%:E < y]) = 0.
Proof.
move=> hi hp hc; pose A := partial_function_preimage f [set y | c%:E < y].
have hA : measure_measurable mu A.
  apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hi.1).
  exact: order_strict_upper_ray_open.
have hAf : forall x, A x -> exists y, partial_function_graph f x y /\ c%:E <= y.
  move=> x [y [hy hcy]]; exists y; split=> //; exact: ltW hcy.
have hb := @nonnegative_threshold_lower_integral_bound R X mu hm A c f hA (ltW hc) hAf hp.
have hlow := @measure_lower_integral_unique R X mu f _ 0
  (measure_lower_integral_specification mu f) hi.2.2.
rewrite hlow in hb.
have hcE : (0 : \bar R) < c%:E by rewrite lte_fin.
have hfin : c%:E \is a fin_num by rewrite fin_numE.
have he := @lee_pmul2l R c%:E hfin hcE (mu A) 0.
rewrite mule0 in he.
have hle : mu A <= 0 by move: hb; rewrite he.
apply/eqP; by rewrite eq_le hle (measure_nonnegative hm).
Qed.

(** Source for [nonnegative_integral_zero_almost_equal]: the zero-integral
    test underlying the equality discussion in Federer 2.4.14, p. 88
    Reciprocal levels give one common conull region; exact partial domains
    are retained. *)
Lemma nonnegative_integral_zero_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_integral mu f 0 ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_equal mu f (partial_function_total (fun _ : X => (0 : extended_real_line R))).
Proof.
move=> hi hp.
pose A n := partial_function_preimage f [set y | (((n.+1)%:R : R)^-1)%:E < y].
have hn n : measure_almost_everywhere mu (~` A n).
  rewrite /measure_almost_everywhere setCK.
  apply: (@nonnegative_integral_zero_superlevel_null R X mu hm f _ hi hp).
  by rewrite invr_gt0 ltr0n.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
  mu hm setT (fun n => ~` A n) (countableP setT) (fun n _ => hn n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hp hall)).
move=> x [[z [hz hz0]] hx].
have hzle : z <= 0.
  apply: (@extended_real_reciprocal_upper_bound R z 0%R)=> n.
  rewrite add0r leNgt; apply/negP=> hlt.
  apply: (hx n I); exists z; by split.
have he : z=0 by apply/eqP; rewrite eq_le hzle hz0.
exists z; split=> //; by rewrite he.
Qed.

(** Source for [nonnegative_integral_zero_iff]: supporting
    equivalence used for the equality cases in Federer
    2.4.14, p. 88. The reverse implication follows
    from null-modification invariance of integrals. *)
Lemma nonnegative_integral_zero_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  (is_measure_integral mu f 0 <->
   measure_almost_equal mu f (partial_function_total (fun _ : X => (0 : extended_real_line R)))).
Proof.
move=> hp; split; first by move=> hi; exact (@nonnegative_integral_zero_almost_equal R X mu hm f hi hp).
move=> he; apply: (@measure_integral_almost_equal R X mu hm _ f 0 (measure_extended_zero_integral hm)).
exact: measure_almost_equal_sym he.
Qed.
