(** Federer (1969), 3.2.7, p. 246, final
    example: summing u(x)=x over fibres of |x|
    gives zero everywhere. Actual positive and negative
    numerical sums are finite and equal on each fibre. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic SummableRealFunctionUP PartialFibreNumericalSum
  NonnegativeSum NonnegativeSumSupport NumericalSum MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureConullZeroIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [absolute_value_signed_fibre_sum_zero]:
    the right integrand in the last counterexample of
    Federer 3.2.7, p. 246. Opposite roots
    cancel, the zero root contributes zero, and
    negative levels have empty fibres. All numerical
    sums are defined by the original signed convention. *)
Theorem absolute_value_signed_fibre_sum_zero (R:realType) (y:R):
  partial_function_graph
    (@partial_fibre_numerical_sum R [the choiceType of real_line_metric R] R
      (fun x:R=>`|x|) (real_total_integrand (fun x:R=>x))) y 0%E.
Proof.
apply/partial_fibre_numerical_sum_graph; exists (fun x:R=>x%:E); split.
- move=>x _; by apply/real_total_integrand_graph.
case:(lerP 0 y)=>hy.
- pose E:=[set x:R | `|x|=y].
  have hPy:E y by rewrite /E /= ger0_norm.
  have hNy:E (-y) by rewrite /E /= normrN ger0_norm.
  have hP:nonnegative_sum E (fun x:R=>extended_positive_part x%:E)=y%:E.
    have hVal:extended_positive_part y%:E=y%:E.
      by rewrite /extended_positive_part max_l // lee_fin.
    rewrite -hVal; apply:nonnegative_sum_single_support=>//.
    - exact:extended_positive_part_nonnegative.
    - move=>x hx hxy; case:(lerP 0 x)=>hx0.
      + have he:x=y by move:hx; rewrite /E /= (ger0_norm hx0).
        by move:hxy; rewrite he eqxx.
      + rewrite /extended_positive_part max_r // lee_fin; exact:ltW hx0.
  have hN:nonnegative_sum E (fun x:R=>extended_negative_part x%:E)=y%:E.
    have hVal:extended_negative_part (-y)%:E=y%:E.
      by rewrite /extended_negative_part -EFinN opprK /extended_positive_part max_l // lee_fin.
    rewrite -hVal; apply:nonnegative_sum_single_support=>//.
    - exact:extended_negative_part_nonnegative.
    - move=>x hx hxy; case:(ltP x 0)=>hx0.
      + have he:x= -y.
          have hh: -x=y by move:hx; rewrite /E /= (ler0_norm (ltW hx0)).
          by rewrite -hh opprK.
        by move:hxy; rewrite he eqxx.
      + rewrite /extended_negative_part -EFinN /extended_positive_part max_r // lee_fin oppr_le0.
        exact hx0.
  change (numerical_sum E (fun x:R=>x%:E)=Some 0%E).
  by rewrite /numerical_sum hP hN /extended_subtract /extended_add /= -EFinD subrr.
- have he:[set x:R | `|x|=y]=set0.
    apply/seteqP; split=>x; last by case.
    move=>hx; have hh:=normr_ge0 x; rewrite hx in hh.
    by have:=le_lt_trans hh hy; rewrite ltxx.
  by rewrite he numerical_sum_empty.
Qed.

(** Source for [absolute_value_signed_fibre_integral_zero]:
    the right integral in the last example of
    Federer 3.2.7, p. 246, exists and is zero
    despite failure of source-weight integrability. *)
Corollary absolute_value_signed_fibre_integral_zero (R:realType):
  is_measure_integral (@lebesgue_scalar_measure R)
    (@partial_fibre_numerical_sum R [the choiceType of real_line_metric R] R
      (fun x:R=>`|x|) (real_total_integrand (fun x:R=>x))) 0%E.
Proof.
have hm:=lebesgue_scalar_is_measure R.
apply:(measure_almost_zero_integral hm).
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_true hm))=>y _.
exact:absolute_value_signed_fibre_sum_zero.
Qed.
