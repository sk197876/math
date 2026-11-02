(** Federer (1969), 2.4.15, p. 89: equality in Minkowski forces both Holder
    estimates in its proof to be attained. These supporting order arguments
    expose the two attained norm-product integrals separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormProduct
  NormPowerScalar RealPower RealPowerSuccessor MeasureMinkowskiPowerEstimate MeasureLpNorm
  MeasureUP MeasurableNormedFunctionUP MeasurableNormedArithmetic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [two_additive_bounds_saturated]: supporting
    scalar equality argument for the last display of Federer
    2.4.15, p. 89. If the sum attains the
    sum of two upper bounds, each bound is attained. *)
Lemma two_additive_bounds_saturated (R : realType) (u v A B : R) :
  (u <= A)%R -> (v <= B)%R -> (A+B <= u+v)%R -> u=A /\ v=B.
Proof.
move=> hu hv hs.
have hAu : (A <= u)%R.
  have h := le_trans hs (lerD (lexx u) hv); by rewrite lerD2r in h.
have hBv : (B <= v)%R.
  have h := le_trans hs (lerD hu (lexx v)); by rewrite lerD2l in h.
by split; apply/eqP; rewrite eq_le ?hu ?hv ?hAu ?hBv.
Qed.

(** Source for [minkowski_equality_holder_integrals]: necessity
    of equality in both Holder estimates in Federer 2.4.15,
    p. 89. All three norms are finite; they
    may vanish. Positivity is needed only in the later
    normalisation step. *)
Lemma minkowski_equality_holder_integrals (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a b c : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu N p g = b%:E ->
  measure_lp_norm mu N p (partial_vector_add f g) = c%:E -> c=(a+b)%R ->
  is_measure_integral mu (partial_norm_product N (fun t : R => `|t|%R) f
    (partial_scalar_norm_power N (p-1)%R (partial_vector_add f g))) (a*real_power c (p-1)%R)%:E /\
  is_measure_integral mu (partial_norm_product N (fun t : R => `|t|%R) g
    (partial_scalar_norm_power N (p-1)%R (partial_vector_add f g))) (b*real_power c (p-1)%R)%:E.
Proof.
move=> hp hf hg hfa hgb hsc hsum.
have hfg := @measurable_normed_function_add R X V N hN mu hm f g hf hg.
have hc0 : (0 <= c)%R.
  have hn := @measure_lp_norm_nonnegative R X V N hN mu p _ hm (ltW hp) hfg.1.
  by move: hn; rewrite hsc lee_fin.
have hr : (0 < p-1)%R by rewrite subr_gt0.
have hid : real_power c p = (c*real_power c (p-1))%R.
  have h := @real_power_positive_successor R c (p-1)%R hc0 hr.
  rewrite subrK in h; by rewrite h mulrC.
have [u [v [hui [hvi [hub [hvb hbnd]]]]]] :=
  @measure_minkowski_holder_integrals R X V N hN mu hm p a b c f g hp hf hg hfa hgb hsc.
have hs : (a*real_power c (p-1)+b*real_power c (p-1) <= u+v)%R.
  by move: hbnd; rewrite hid hsum mulrDl.
have [heu hev] := @two_additive_bounds_saturated R u v _ _ hub hvb hs.
by rewrite heu in hui; rewrite hev in hvi; split.
Qed.
