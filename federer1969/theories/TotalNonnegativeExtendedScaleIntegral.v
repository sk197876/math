(** Supporting infinite-value averaging in Federer (1969), 2.10.16, p. 178:
    a nonnegative extended constant factors out of the actual integral of a
    total nonnegative function. The infinite case is the constant-series
    case of 2.4.8, p. 84, with the zero-infinity convention of 2.4.4(2), p.
    82. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence
  MeasureConullZeroIntegral MeasureAlmostUP MeasureAlmostBasic MeasureUpperIntegralScale
  TotalNonnegativeSeriesIntegral NonnegativeSeriesConstant NonnegativeExtendedNormOrder NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_nonnegative_extended_scale_integral]:
    supporting extended constant factor for the averages of
    2.10.16, p. 178. The hypotheses make total domains
    and nonnegative values explicit, so zero times infinity
    and infinity times a null integral both retain value zero. *)
Theorem total_nonnegative_extended_scale_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) a c :
  (forall x, 0<=f x) -> is_measure_integral mu (partial_function_total f) a -> 0<=c ->
  is_measure_integral mu (partial_function_total (fun x => (c*f x : extended_real_line R))) (c*a).
Proof.
move=> hp hi; case: c=> [r| |] hc; last by [].
- have hr : (0<=r)%R by move: hc; rewrite lee_fin.
  case: (eqVneq r 0%R)=> [->|hne].
  + rewrite mul0e; apply: (measure_almost_zero_integral hm).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
    by rewrite /partial_function_total /= mul0e.
  + have hrpos : (0<r)%R by rewrite lt_def hne hr.
    have hs := @measure_integral_positive_scale R X mu hm r (partial_function_total f) a hrpos hi.
    apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hs)=> x y.
    split; first by move=> [z [<- <-]].
    move=> hy; exists (f x); by split.
- have ha : 0<=a := @nonnegative_total_integral_value_ge0 R X mu hm f a hp hi.
  have hs := @total_nonnegative_series_integral R X mu hm (fun _ : nat => f) (fun _ : nat => a)
    (fun _ x => hp x) (fun _ => hi).
  rewrite (nonnegative_series_constant ha) in hs.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hs)=> x y.
  change (nonnegative_sum setT (fun _ : nat => f x)=y <-> +oo*f x=y).
  by rewrite (nonnegative_series_constant (hp x)).
Qed.
