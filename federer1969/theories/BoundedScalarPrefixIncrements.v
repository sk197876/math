(** Federer (1969), 3.2.33, p. 270: monotonicity
    and the unit Lipschitz bound for the actual primitive g. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureSubsetIntegral LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  RealSegmentIntegralDifference FiniteSubsetRealConstantBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_scalar_prefix_increment]: supporting
    the increasing g in Federer 3.2.33, p. 270.
    Since 0<=psi<= 1, actual integral additivity and finite
    constant bounds prove 0<=g(b)-g(a)<=b-a on [0,1].
    This also supplies the Lipschitz hypothesis required by
    the example's reference to 3.2.32. *)
Lemma bounded_scalar_prefix_increment (R:realType) (psi g:R->R):
  (forall t,0<=psi t<= 1) ->
  (forall t,0<=t<= 1 ->is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,t]
    (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R))) (g t)%:E) ->
  forall a b:R,0<=a ->a<=b ->b<= 1 ->0<=g b-g a<=b-a.
Proof.
move=>hBounds hPrimitive a b ha hab hb.
have hm:=lebesgue_scalar_is_measure R.
have ha1:a<= 1:=le_trans hab hb.
have hb0:0<=b:=le_trans ha hab.
have hI:=@lebesgue_segment_integral_finite_difference R
  (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R)))
  0 a b (g a) (g b) ha hab (hPrimitive a (ltac:(by apply/andP; split)))
  (hPrimitive b (ltac:(by apply/andP; split))).
have hSet:measure_measurable (@lebesgue_scalar_measure R) `[a,b].
  apply:(@borel_regular_borel_measurable R (real_line_metric R) (@lebesgue_scalar_measure R)
    hm (lebesgue_scalar_borel_regular R)).
  exact:(closed_borel_set (@segment_closed_real R a b)).
have hBound:=@finite_subset_real_constant_bounds R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[a,b] psi (b-a) (g b-g a) 0 1
  hSet (lebesgue_scalar_segment hab) (fun t _=>hBounds t) hI.
by rewrite mul0r mul1r in hBound.
Qed.
