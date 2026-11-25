(** Federer (1969), 3.2.35, p. 272:
    finite summation of the nonnegative projected
    volume integrals in Steiner's induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP
  TotalCountableNonnegativeIntegral NonnegativeSum FiniteCoverMeasureBounds NonnegativeExtendedNormOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_finite_nonnegative_integral]:
    supporting finite integral interchange in
    Federer 3.2.35, p. 272, from the
    already proved 2.4.8, p. 84. Actual
    nonnegative extended summands and their
    integrals may be infinite; the finite
    type may be empty. No interchange law
    is introduced as an assumption. *)
Lemma total_finite_nonnegative_integral (R:realType) (X:choiceType) (I:finType)
    (mu:set X->\bar R) (hm:is_measure mu)
    (u:I->X->extended_real_line R) (a:I->\bar R):
  (forall i x,0<=u i x) ->
  (forall i,is_measure_integral mu (partial_function_total (u i)) (a i)) ->
  is_measure_integral mu (partial_function_total (fun x=>(\sum_i u i x:extended_real_line R))) (\sum_i a i).
Proof.
move=>hu hi.
have hNonnegative i:0<=a i:=@nonnegative_total_integral_value_ge0 R X mu hm (u i) (a i) (hu i) (hi i).
have hSum:=@total_countable_nonnegative_integral R X I mu hm setT u a
  (countableP _) (fun i _=>hu i) (fun i _=>hi i).
have hFunction:(fun x=>nonnegative_sum setT (fun i=>u i x))=(fun x=>\sum_i u i x).
  apply:funext=>x; exact:finite_type_nonnegative_sum (fun i=>hu i x).
have hValues:nonnegative_sum setT a=\sum_i a i:=finite_type_nonnegative_sum hNonnegative.
by rewrite hFunction hValues in hSum.
Qed.
