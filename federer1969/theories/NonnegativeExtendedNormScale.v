(** Federer (1969), 2.4.12, pp. 86–87: supporting homogeneity of the
    nonnegative extended-input norm used for the integral-geometric
    application of 2.10.24, p. 188. Reduce a finite norm to an almost
    everywhere finite scalar representative; infinite input values are
    retained until their exceptional set is proved null. The zero scalar
    uses the convention zero times infinity equals zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity
  ScalarNormExtendedEmbedding ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic MeasurableGraphEquivalence
  MeasureUpperIntegralScale MeasurableExtendedScale
  NonnegativeExtendedExponentNorm NonnegativeExtendedScalarNorm
  NonnegativeExtendedNormAlmostEquality NonnegativeExtendedNormFiniteValues
  NonnegativeExtendedNormZero ProbabilityNonnegativeExtendedNorm
  TotalScalarLpUP TotalScalarLpNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_extended_scale]: supporting
    measurable scalar multiplication from 2.4.4(3), p. 82,
    for the norm operation in 2.4.12, pp. 86–87.
    The zero scalar produces the total zero function under
    the convention of 2.4.2, p. 81. *)
Lemma measurable_total_extended_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (a : R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x=>a%:E*f x)).
Proof.
move=> hf; case: (eqVneq a 0%R)=> [->|hane].
- have he : (fun x=>0%:E*f x)=(fun _ : X=>(0 : extended_real_line R)).
    by apply: funext=> x; rewrite mul0e.
  rewrite he; exact: measurable_total_constant.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu
  (partial_extended_function_scale a (partial_function_total f)) _ _
  (@measurable_extended_nonzero_scale R X mu hm a _ hane hf))=> x y.
split.
- move=> [z [hz hy]]; by rewrite -hz in hy.
- move=> hy; exists (f x); by split.
Qed.

(** Source for [nonnegative_extended_norm_scale_bound]: supporting
    positive homogeneity bound from the seminorm assertion
    in 2.4.12, pp. 86–87, for the weighted
    integral-geometric construction of 2.10.24, p. 188.
    Every exponent at least one, including infinity, and
    every finite nonnegative scalar, including zero, are
    allowed. No finiteness or sigma-finiteness of the
    underlying measure is imposed. *)
Theorem nonnegative_extended_norm_scale_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (p : \bar R) (a : R) :
  (forall x, 0<=f x) -> 1<=p -> (0<=a)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu (fun x=>a%:E*f x) p<=
    a%:E*nonnegative_extended_exponent_norm mu f p.
Proof.
move=> hf0 hp ha hf.
have haE : 0<=a%:E by rewrite lee_fin.
case: (eqVneq a 0%R)=> [->|hane].
- have he : (fun x=>0%:E*f x)=(fun _ : X=>(0 : extended_real_line R)).
    by apply: funext=> x; rewrite mul0e.
  rewrite he mul0e.
  have hz : nonnegative_extended_exponent_norm mu (fun _ : X=>(0 : extended_real_line R)) p=0.
    apply: (@nonnegative_extended_norm_zero_iff R X mu hm _ p (fun _=>lexx _) hp
      (@measurable_total_constant R X (extended_real_line R) mu hm 0)).2.
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
      (measure_almost_everywhere_true hm))=> x _; reflexivity.
  by rewrite hz.
have hap : (0<a)%R by rewrite lt_neqAle eq_sym hane ha.
case: (ltP (nonnegative_extended_exponent_norm mu f p) +oo)=> [hfin|hinf]; last first.
  have he : nonnegative_extended_exponent_norm mu f p=+oo.
    by apply/eqP; rewrite eq_le hinf leey.
  by rewrite he /mule /= eqe lte_fin (gt_eqF hap) hap leey.
have hn := @nonnegative_extended_exponent_norm_specification R X mu f p hm hf0 hp hf.
have hfinite := @finite_nonnegative_extended_norm_almost_finite R X mu hm f p _ hf0 hn hfin.
pose g (x : X) : real_norm_metric_space (scalar_absolute_value_norm R) := fine (f x).
have hg := @measurable_extended_finite_scalar R X mu hm f hf.
have hg0 x : (0<=g x)%R.
  rewrite /g; have h := hf0 x; by case: (f x) h=> [r| |] //=; rewrite lee_fin.
have hscaled : @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x=>a%:E*f x)).
  exact: (@measurable_total_extended_scale R X mu hm f a hf).
have hag : @is_measure_measurable_function R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu
    (partial_function_total (fun x=>(a*g x)%R)).
  apply: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    mu hm g (fun y=>(a*y)%R) hg).
  apply: continuous_borel_function.
  exact: (@real_norm_metric_scale_continuous R R^o (fun y=>`|y|%R) (scalar_absolute_value_norm R) a).
have hag0 x : (0<=a*g x)%R := mulr_ge0 ha (hg0 x).
have hage : @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x=>(a*g x)%R%:E)).
  apply: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hm (fun x=>(a*g x)%R) (fun y=>y%:E) hag).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hae : measure_almost_everywhere mu [set x | a%:E*f x=(a*g x)%R%:E].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfinite)=> x hx.
  change (a%:E*f x=(a*fine (f x))%R%:E).
  by rewrite EFinM (fineK hx).
rewrite (@nonnegative_extended_norm_almost_equal R X mu hm
  (fun x=>a%:E*f x) (fun x=>(a*g x)%R%:E) p
  (fun x=>mule_ge0 haE (hf0 x)) (fun x=>hag0 x) hp hscaled hage hae)
  (@nonnegative_extended_norm_scalar_embedding R X mu hm (fun x=>(a*g x)%R) p hag0 hp hag).
have hs := @total_scalar_lp_norm_scale R X mu hm p a g hp hg.
rewrite /total_scalar_lp_norm /total_scalar_function (ger0_norm ha) in hs.
rewrite hs (@nonnegative_extended_norm_almost_finite_scalar R X mu hm f p hf0 hfinite hp hf).
exact: lexx.
Qed.

(** Source for [nonnegative_extended_norm_scale]: supporting
    exact homogeneity of the norm in 2.4.12, pp. 86–87,
    for the weighted integral-geometric estimate in 2.10.24,
    p. 188. Positive inverse scaling proves the reverse
    inequality; zero weights retain the printed zero-product
    convention. The input may take infinite values. *)
Theorem nonnegative_extended_norm_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (p : \bar R) (a : R) :
  (forall x, 0<=f x) -> 1<=p -> (0<=a)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu (fun x=>a%:E*f x) p=
    a%:E*nonnegative_extended_exponent_norm mu f p.
Proof.
move=> hf0 hp ha hf.
have hle := @nonnegative_extended_norm_scale_bound R X mu hm f p a hf0 hp ha hf.
apply/eqP; rewrite eq_le hle /=.
case: (eqVneq a 0%R)=> [->|hane].
- rewrite mul0e.
  apply: (@nonnegative_extended_exponent_norm_ge0 R X mu _ p hm _ hp
    (@measurable_total_extended_scale R X mu hm f 0%R hf))=> x.
  by rewrite mul0e.
have hscaled := @measurable_total_extended_scale R X mu hm f a hf.
have haE : 0<=a%:E by rewrite lee_fin.
have hai : (0<=a^-1)%R by rewrite invr_ge0.
have hback := @nonnegative_extended_norm_scale_bound R X mu hm
  (fun x=>a%:E*f x) p (a^-1)%R
  (fun x=>mule_ge0 haE (hf0 x)) hp hai hscaled.
have he : (fun x=>(a^-1)%R%:E*(a%:E*f x))=f.
  by apply: funext=> x; rewrite muleA -EFinM mulVf // mul1e.
have hh := lee_wpmul2l haE hback.
by rewrite he muleA -EFinM mulfV // mul1e in hh.
Qed.
