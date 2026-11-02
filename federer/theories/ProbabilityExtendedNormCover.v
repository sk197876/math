(** Supporting countable cost-cover inequality for Federer (1969), 2.10.9,
    p. 175. If f is pointwise dominated by a countable sum of nonnegative
    measurable inputs, its probability Lp norm is at most the sum of their
    norms. When that sum is finite, prove finiteness of every input almost
    everywhere, construct the scalar Lp sum as an existence proof, and
    compare only on a common conull set. The arguments are the triangle and
    lower-limit laws of 2.4.12, pp. 86–87, and the increasing scalar
    replacement used in 2.5.7, p. 98. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ScalarNormExtendedEmbedding ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic TotalScalarLpUP NonnegativeSum NonnegativeSumSupport
  NonnegativeExtendedExponentNorm NonnegativeExtendedScalarNorm NonnegativeExtendedNormFiniteValues
  NonnegativeExtendedNormOrder ProbabilityScalarLpMembership ScalarLpCountablePositiveBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_nonnegative_extended_norm_cover]:
    supporting countable triangle comparison for the integral-
    geometric cost hypothesis in Federer 2.10.9, p. 175.
    Countable repeated indices, empty index sets, infinite
    input values and the infinity exponent are allowed. No
    finite-norm hypothesis is imposed in the statement. *)
Theorem probability_nonnegative_extended_norm_cover (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R)
    (D : set J) (f : X -> extended_real_line R) (F : J -> X -> extended_real_line R) :
  mu setT = 1 -> countable D -> 1<=t ->
  (forall x, 0<=f x) -> (forall j x, 0<=F j x) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall j, D j -> is_measure_measurable_function mu (partial_function_total (F j))) ->
  (forall x, f x<=nonnegative_sum D (fun j => F j x)) ->
  nonnegative_extended_exponent_norm mu f t<=
    nonnegative_sum D (fun j => nonnegative_extended_exponent_norm mu (F j) t).
Proof.
move=> hprob hD ht hf0 hF0 hf hF hcover.
pose a := nonnegative_sum D (fun j => nonnegative_extended_exponent_norm mu (F j) t).
case: (ltP a +oo)=> [hfin|hinf]; last exact: le_trans (leey _) hinf.
have hnormfin j : D j -> nonnegative_extended_exponent_norm mu (F j) t< +oo.
  move=> hj; exact: le_lt_trans (nonnegative_sum_term _ hj) hfin.
pose u j x := fine (F j x).
have hu j : D j -> total_scalar_lp mu t (u j).
  move=> hj; exact: (@probability_extended_finite_norm_scalar_lp R X mu hm (F j) t
    hprob (hF0 j) ht (hF j hj) (hnormfin j hj)).1.
have hu0 j x : (0<=u j x)%R.
  rewrite /u; have h := hF0 j x; by case: (F j x) h=> [r| |] //=; rewrite lee_fin.
have hunorm j : D j -> total_scalar_lp_norm mu t (u j)=nonnegative_extended_exponent_norm mu (F j) t.
  move=> hj; exact: (@probability_extended_finite_norm_scalar_lp R X mu hm (F j) t
    hprob (hF0 j) ht (hF j hj) (hnormfin j hj)).2.
have hsum : nonnegative_sum D (fun j => total_scalar_lp_norm mu t (u j))=a.
  apply: nonnegative_sum_ext=> j hj; exact: hunorm.
have hufin : nonnegative_sum D (fun j => total_scalar_lp_norm mu t (u j))< +oo by rewrite hsum.
have [g [hg [hg0 [hgnorm hgsum]]]] := @scalar_lp_countable_positive_bound R X J mu hm t D u
  hD ht hu hu0 hufin.
have hfinite j : D j -> measure_almost_everywhere mu [set x | F j x \is a fin_num].
  move=> hj; exact: (@finite_nonnegative_extended_norm_almost_finite R X mu hm (F j) t _
    (hF0 j) (@nonnegative_extended_exponent_norm_specification R X mu (F j) t hm
      (hF0 j) ht (hF j hj)) (hnormfin j hj)).
have hall := @measure_almost_everywhere_countable R X J mu hm D
  (fun j => [set x | F j x \is a fin_num]) hD hfinite.
have hfg : measure_almost_everywhere mu [set x | f x<=(g x)%:E].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hall hgsum))=> x [hx hsumx].
  have he : nonnegative_sum D (fun j => F j x)=nonnegative_sum D (fun j => (u j x)%:E).
    apply: nonnegative_sum_ext=> j hj; exact: esym (fineK (hx j hj)).
  have hb := hcover x; by rewrite he hsumx in hb.
have hge : @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x => (g x)%:E)).
  apply: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hm g (fun y => y%:E) hg.2.1).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hb := @nonnegative_extended_norm_almost_order R X mu hm f (fun x => (g x)%:E) t
  hf0 (fun x => (hg0 x : 0<=(g x)%:E)) ht hf hge hfg.
rewrite (@nonnegative_extended_norm_scalar_embedding R X mu hm g t hg0 ht hg.2.1) in hb.
apply: le_trans hb _; by rewrite -/a -hsum.
Qed.
