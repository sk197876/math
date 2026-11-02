(** Supporting zero-norm criterion for Federer (1969), 2.10.5, p. 173,
    common null sets of integral-geometric measures. Extend the scalar
    zero-norm criterion of 2.4.12, p. 86, and 2.4.17, p. 90, to nonnegative
    extended inputs. A zero norm first gives finite values almost
    everywhere; only then use the proved exact scalar reduction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureExponentZero
  MeasureExponentDomain NonnegativeExtendedExponentNorm NonnegativeExtendedNormFiniteValues
  NonnegativeExtendedScalarNorm ProbabilityNonnegativeExtendedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_norm_zero_iff]:
    supporting independence of the zero numerator
    from t for Federer 2.10.5, p. 173.
    Every t>=1, including infinity, has zero
    norm exactly when the actual nonnegative
    extended input vanishes almost everywhere. *)
Theorem nonnegative_extended_norm_zero_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  (nonnegative_extended_exponent_norm mu f t=0 <->
   measure_almost_everywhere mu [set x | f x=0]).
Proof.
move=> hf0 ht hf.
pose g (x : X) : real_norm_metric_space (scalar_absolute_value_norm R) := fine (f x).
have hg := @measurable_extended_finite_scalar R X mu hm f hf.
have hscalar := @measure_exponent_norm_zero_iff R X mu hm g t ht hg.
split.
- move=> hz.
  have hs := @nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf.
  have hnfin : nonnegative_extended_exponent_norm mu f t < +oo by rewrite hz ltry.
  have hfinite := @finite_nonnegative_extended_norm_almost_finite R X mu hm f t _ hf0 hs hnfin.
  have he := @nonnegative_extended_norm_almost_finite_scalar R X mu hm f t hf0 hfinite ht hf.
  have hgz : measure_almost_everywhere mu [set x | g x=0%R].
    apply: hscalar.1; by rewrite -he.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hfinite hgz))=> x [hfx hgx].
  have heq : f x=(g x)%:E := esym (fineK hfx).
  change (f x=0); by rewrite heq hgx.
- move=> hz.
  have hfinite : measure_almost_everywhere mu [set x | f x \is a fin_num].
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hz)=> x hx.
    change (is_true (f x \is a fin_num)); by rewrite hx fin_numE.
  have hgz : measure_almost_everywhere mu [set x | g x=0%R].
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hz)=> x hx.
    change (g x=0%R); by rewrite /g hx.
  rewrite (@nonnegative_extended_norm_almost_finite_scalar R X mu hm f t hf0 hfinite ht hf).
  exact: hscalar.2 hgz.
Qed.
