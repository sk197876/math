(** Federer (1969), 2.6.2, p. 117: the null-set step of the Fubini proof.
    This supporting version extracts an almost-everywhere zero conclusion
    from measurable majorants with arbitrarily small nonnegative integrals.
    It uses the countable infimum of 2.3.2, p. 74, and integral comparison
    from 2.4.4, pp. 82–83. Our direct cover-majorant argument is a
    documented proof variation, not an additional source theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds
  PartialFunctionUP PartialFunctionBasic PartialFunctionSupremumUP
  PartialFunctionInfimumUP PartialFunctionInfimumSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP MeasurableCountableInfimum PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison
  MeasureNonnegativeIntegral MeasureNonnegativeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [vanishing_integral_majorants_almost_zero]: local
    supporting lemma for Federer 2.6.2's null-set step, p. 117.
    A nonnegative function dominated pointwise by measurable
    nonnegative functions whose integrals tend to zero vanishes
    almost everywhere. No measurability of the dominated function
    is assumed. Reciprocal bounds express the convergence to zero. *)
Lemma vanishing_integral_majorants_almost_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : nat -> X -> extended_real_line R) (a : nat -> \bar R) (v : X -> \bar R) :
  (forall n x, 0 <= u n x) ->
  (forall n, is_measure_integral mu (partial_function_total (u n)) (a n)) ->
  (forall n, a n <= (((n.+1)%:R : R)^-1)%:E) ->
  (forall x, 0 <= v x) -> (forall n x, v x <= u n x) ->
  measure_almost_everywhere mu [set x | v x = 0].
Proof.
move=> hu hi ha hv hvu.
pose f n := partial_function_total (u n).
pose g := @PartialFunctionInfimum.value R X nat setT f.
have hg : is_partial_function_infimum setT f g := @PartialFunctionInfimum.laws R X nat setT f.
have hd x : partial_function_domain g x.
  rewrite (partial_function_infimum_domain hg); move=> n _.
  by exists (u n x).
have hgl x z (hz : partial_function_graph g x z) n : z <= u n x.
  apply: (@partial_function_infimum_lower R X nat setT f g hg x z hz).
  exists n; by split.
have hgz x z (hz : partial_function_graph g x z) : 0 <= z.
  apply: (@partial_function_infimum_greatest R X nat setT f g hg x z hz)=> y [n [_ hy]].
  rewrite -(hy : u n x = y); exact: hu.
have hgm : is_measure_measurable_function mu g.
  apply: (@measurable_countable_infimum R X [the choiceType of (nat : Type)] mu hm setT f g
    (countableP setT) _ hg)=> n _; exact: (hi n).1.
have hgp : measure_almost_everywhere mu (partial_extended_nonnegative_locus g).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; have [z hz] := hd x; exists z; split=> //; exact: hgz hz.
have [hgi hnon] := @nonnegative_measurable_function_integral R X mu hm g hgm hgp.
have hzero : measure_lower_integral mu g = 0.
  apply/eqP; rewrite eq_le hnon andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> n; rewrite add0r.
  apply: le_trans _ (ha n).
  apply: (@measure_integral_monotone R X mu hm g (f n) _ _ hgi (hi n)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; have [z hz] := hd x; exists z, (u n x); split=> //; split=> //; exact: hgl hz n.
rewrite hzero in hgi.
have hz := @nonnegative_integral_zero_almost_equal R X mu hm g hgi hgp.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hz).
move=> x [z [hzg hzz]]; have ez : z = 0 by exact: esym hzz.
apply/eqP; rewrite eq_le (hv x) andbT -ez.
apply: (@partial_function_infimum_greatest R X nat setT f g hg x z hzg)=> y [n [_ hy]].
rewrite -(hy : u n x = y); exact: hvu.
Qed.
