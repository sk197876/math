(** Federer (1969), 2.4.11, proof p. 86: on A, |f| is bounded by the
    truncation tail plus n times the characteristic function of A; off A the
    zero extension is bounded by the nonnegative tail. This gives the
    printed integral estimate without needing an additional exact-domain
    cancellation for exceptional infinite values. Source context:
    PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialUpperTruncation PartialExtendedArithmetic PartialZeroExtension PartialExtendedOrderLoci
  CharacteristicFunctionUP MeasureStepIntegralIdentification DominatedErrorGraphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [truncation_subset_pointwise_bound]: supporting
    pointwise inequality for the last estimate in Federer
    2.4.11, proof p. 86. It is used on
    the conull region where the summable function is finite. *)
Lemma truncation_subset_pointwise_bound (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (A : set X)
    (s : X -> real_line_metric R) (c y : R) x :
  is_characteristic_function A s -> (0 <= c)%R -> partial_function_graph f x y%:E ->
  partial_extended_le_locus (partial_function_zero_extension (0 : extended_real_line R) A f)
    (partial_extended_function_add
      (partial_extended_function_subtract f (partial_upper_truncation f c%:E))
      (partial_real_function_embed (partial_function_total (fun x => ((c*s x)%R : real_line_metric R))))) x.
Proof.
move=> hs hc hy; pose v := Num.min y c.
have hvg : partial_function_graph (partial_upper_truncation f c%:E) x v%:E.
  exists y%:E; split=> //; by rewrite /v EFin_min.
have htail := @partial_finite_difference_graph R X f (partial_upper_truncation f c%:E) x y v hy hvg.
have hchar : partial_function_graph (partial_real_function_embed
    (partial_function_total (fun x => ((c*s x)%R : real_line_metric R)))) x (c*s x)%:E.
  exists (c*s x)%R; by split.
have hsum := @partial_finite_sum_graph R X _ _ x (y-v)%R (c*s x)%R htail hchar.
have hvy : (v <= y)%R by rewrite /v ge_min lexx orTb.
have hvc : (v <= c)%R by rewrite /v ge_min lexx orbT.
have [hx|hx] := pselect (A x).
- exists y%:E,(y-v+c*s x)%:E; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; rewrite (characteristic_on_set hs hx) mulr1 lee_fin.
    have hbound : (y-v+v <= y-v+c)%R by rewrite lerD2l.
    by rewrite subrK in hbound.
- exists 0,(y-v+c*s x)%:E; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split=> //; by rewrite (characteristic_off_set hs hx) mulr0 addr0 lee_fin subr_ge0.
Qed.
