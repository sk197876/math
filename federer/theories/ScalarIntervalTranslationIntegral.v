(** Federer (1969), 2.7.16(1), pp. 134--135, and
    2.4.18(1), p. 90: translation of the genuine scalar
    parameter integral, supporting concatenation of curves
    in 3.2.46, p. 281. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  ScalarAffineLebesgue LebesgueScalarMeasure MeasureUP MeasurePushforward
  PartialFunctionUP PartialFunctionPrecomposition MeasureSubsetIntegral
  InvariantSubsetIntegralTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_translation_pushforward]: translation
    preserves actual scalar Lebesgue measure on every set,
    by Federer 2.7.16(1), p. 135. Supporting the translated
    second curve in the triangle argument of 3.2.46, p. 281. *)
Lemma scalar_translation_pushforward (R : realType) (d : R) :
  measure_pushforward (fun t : real_line_metric R => t+d)
    (@lebesgue_scalar_measure R) = @lebesgue_scalar_measure R.
Proof.
apply: funext=> T.
have he : (fun t : real_line_metric R=>t+d) @^-1` T =
    (fun t : real_line_metric R=>1*t+(-d)) @` T.
  apply/seteqP; split=> t.
  - move=> ht; exists (t+d); first exact: ht; ring.
  - move=> [s hs <-]; have hInv : (1*s+(-d))+d=s by ring.
    change (T ((1*s+(-d))+d)); by rewrite hInv.
have hSlope : (1 : R) != 0 by rewrite oner_eq0.
have hImage := @scalar_affine_lebesgue_image R 1 (-d) T hSlope.
by rewrite /measure_pushforward he hImage normr1 mul1e.
Qed.

(** Source for [scalar_interval_translation_integral]: the
    actual integral over [a,b] is the translated integral over
    [a-d,b-d], supporting concatenation in Federer 3.2.46,
    p. 281. Both partial definedness and values are retained. *)
Lemma scalar_interval_translation_integral (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (a b d : R) v :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b] f v ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a-d,b-d]
    (partial_function_precompose (fun t=>t+d) f) v.
Proof.
move=> hIntegral.
have hInj : injective (fun t : real_line_metric R=>t+d).
  by move=> t u h; exact: (addIr d) h.
have hTransport := @invariant_subset_integral_transport R
  [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (fun t=>t+d) `[a,b] f v
  hInj (scalar_translation_pushforward d) hIntegral.
have he : (fun t : real_line_metric R=>t+d) @^-1` `[a,b] = `[a-d,b-d].
  apply/seteqP; split=> t.
  - change (is_true (a <= t+d <= b) -> is_true (a-d <= t <= b-d)).
    move=> /andP [h1 h2]; apply/andP; split; lra.
  - change (is_true (a-d <= t <= b-d) -> is_true (a <= t+d <= b)).
    move=> /andP [h1 h2]; apply/andP; split; lra.
by rewrite he in hTransport.
Qed.
