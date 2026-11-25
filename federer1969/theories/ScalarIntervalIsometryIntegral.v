(** Federer (1969), 2.4.18, pp. 90--91, and 2.7.16(1),
    pp. 134--135: scalar translations and reflections preserve
    Lebesgue integrals. These supporting changes of parameter are
    used for the genuine curves in 3.2.46, p. 281. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  ScalarAffineLebesgue LebesgueScalarMeasure MeasureUP MeasurePushforward
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_reflection_shift_pushforward]: reversing
    a compact-interval parameter preserves scalar Lebesgue measure,
    supporting the symmetry of rho in Federer 3.2.46, p. 281,
    by the actual affine invariance of 2.7.16(1), p. 135. *)
Lemma scalar_reflection_shift_pushforward (R : realType) (c : R) :
  measure_pushforward (fun t : real_line_metric R => c-t)
    (@lebesgue_scalar_measure R) = @lebesgue_scalar_measure R.
Proof.
apply: funext=> T.
have he : (fun t : real_line_metric R => c-t) @^-1` T =
    (fun t : real_line_metric R => -1*t+c) @` T.
  apply/seteqP; split=> t.
  - move=> ht; exists (c-t); first exact: ht; ring.
  - move=> [s hs <-]; have hInv : c-(-1*s+c)=s by ring.
    change (T (c-(-1*s+c))); by rewrite hInv.
have hSlope : (-1 : R) != 0 by rewrite oppr_eq0 oner_eq0.
have hImage := @scalar_affine_lebesgue_image R (-1) c T hSlope.
by rewrite /measure_pushforward he hImage normrN normr1 mul1e.
Qed.

(** Source for [scalar_interval_reflection_integral]: the
    actual subset integral is unchanged by t |-> a+b-t,
    supporting reversal of the interval curves in Federer
    3.2.46, p. 281. Missing partial values remain missing. *)
Lemma scalar_interval_reflection_integral (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (a b : R) v :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b] f v ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (partial_function_precompose (fun t => a+b-t) f) v.
Proof.
move=> hIntegral.
pose u := fun t : real_line_metric R => a+b-t.
have hCancel : cancel u u by move=> t; rewrite /u; ring.
have hInterval t : (`[a,b] : set (real_line_metric R)) (u t) <->
    (`[a,b] : set (real_line_metric R)) t.
  rewrite /u /mkset !in_itv /=; split=> /andP [h1 h2]; apply/andP; split; lra.
have hPush : measure_pushforward u (@lebesgue_scalar_measure R) =
    @lebesgue_scalar_measure R := scalar_reflection_shift_pushforward (a+b).
have hTransport := (@injective_pushforward_integral_iff R
  [the choiceType of real_line_metric R] [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) u
  (partial_function_zero_extension (0 : extended_real_line R) `[a,b] f)
  (can_inj hCancel) v).2.
rewrite hPush in hTransport.
have hComp := hTransport hIntegral.
apply: (measure_integral_graph_equivalent _ hComp)=> t z.
change (partial_function_graph (partial_function_zero_extension (0 : extended_real_line R)
  `[a,b] f) (u t) z <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R)
  `[a,b] (partial_function_precompose u f)) t z).
rewrite !partial_function_zero_extension_graph.
split; move=> [[ht hz]|[ht hz]].
- left; by split; [exact: (hInterval t).1 ht |].
- right; split=> // ht'; exact: ht ((hInterval t).2 ht').
- left; by split; [exact: (hInterval t).2 ht |].
- right; split=> // ht'; exact: ht ((hInterval t).1 ht').
Qed.
