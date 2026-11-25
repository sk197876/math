(** Federer (1969), 4.1.2, p. 348: the
    tagged finite Borel sums have their actual vector
    integrals and approximate the original integral with
    a uniform cell-error bound. This is the original
    partition argument, with all zero cells retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureBasic MeasureIntegralUP MeasureCharacteristicIntegral
  MeasureVectorIntegralUP MeasureVectorCharacteristicIntegral SummableRealFunctionUP SummableRealArithmetic
  TotalVectorIntegralArithmetic TotalVectorIntegralFiniteSum TotalVectorIntegralEstimate FiniteTaggedBorelPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteTaggedVectorIntegral.
Variable R:realType.
Variable X:metricType R.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable K:set X.
Variable b:R.
Hypothesis hMass:mu K=b%:E.
Hypothesis hKMeas:measure_measurable mu K.
Variable mesh:R.
Variable I:finType.
Variable A:I->set X.
Variable tag:I->X.
Hypothesis hPart:is_finite_tagged_borel_partition K mesh A tag.
Hypothesis hAMeas:forall i,measure_measurable mu (A i).
Local Notation chi := (fun i=>@CharacteristicFunction.value R X (A i)).
Local Notation chiK := (@CharacteristicFunction.value R X K).
Local Notation mass := (fun i=>fine (mu (A i))).

(** Source for [finite_tagged_partition_mass_value]: every original
    cell has its actual finite measure, including zero,
    in the sums of Federer 4.1.2, p. 348. *)
Theorem finite_tagged_partition_mass_value i:mu (A i)=(mass i)%:E.
Proof.
have hZero:=measure_nonnegative hm (A i).
have hUpper:=measure_mono hm (@finite_tagged_partition_inside R X K mesh I A tag hPart i).
have hFinite:(mu (A i)< +oo)%E.
  apply:le_lt_trans hUpper _; by rewrite hMass ltry.
have hFin:mu (A i) \is a fin_num by rewrite ge0_fin_numE.
by rewrite fineK.
Qed.

(** Source for [finite_tagged_step_on_cell]: on each original
    partition cell the finite step sum has exactly the
    tagged value, Federer 4.1.2, p. 348. *)
Theorem finite_tagged_step_on_cell (F:X->Y) i x:A i x ->
  (\sum_j chi j x*:F (tag j))=F (tag i).
Proof.
move=>hx; rewrite (bigD1 i) //=.
rewrite (characteristic_on_set (@CharacteristicFunction.laws R X (A i)) hx) scale1r.
have hOther:(\sum_(j|j!=i) chi j x*:F (tag j))=0.
  apply:big1=>j hji.
  have hNo:~A j x.
    move=>hj.
    have hEqual:=@finite_tagged_partition_disjoint R X K mesh I A tag hPart j i x hj hx.
    by move:hji; rewrite hEqual eqxx.
  by rewrite (characteristic_off_set (@CharacteristicFunction.laws R X (A j)) hNo) scale0r.
by rewrite hOther addr0.
Qed.

(** Source for [finite_tagged_step_off_compact]: the original
    finite partition sum vanishes off the compact support,
    Federer 4.1.2, p. 348. *)
Theorem finite_tagged_step_off_compact (F:X->Y) x:~K x ->
  (\sum_j chi j x*:F (tag j))=0.
Proof.
move=>hx; apply:big1=>j _.
have hNo:~A j x by move=>hj; apply:hx; exact:(@finite_tagged_partition_inside R X K mesh I A tag hPart j x hj).
by rewrite (characteristic_off_set (@CharacteristicFunction.laws R X (A j)) hNo) scale0r.
Qed.

(** Source for [finite_tagged_vector_sum_integral]: the vector
    integral of the tagged step field is the original
    finite sum of cell masses times tagged values,
    Federer 4.1.2, p. 348. *)
Theorem finite_tagged_vector_sum_integral (F:X->Y):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(\sum_i chi i x*:F (tag i):real_norm_metric_space hNY)))
    (\sum_i mass i*:F (tag i)).
Proof.
apply:(@total_vector_integral_finite_sum R X Y NY hNY mu hm I
  (fun i x=>chi i x*:F (tag i)) (fun i=>mass i*:F (tag i)))=>i.
exact:(@measure_vector_characteristic_integral R X Y NY hNY mu hm (A i)
  (fun x=>(chi i x:real_line_metric R)) (mass i) (F (tag i))
  (@CharacteristicFunction.laws R X (A i)) (hAMeas i) (finite_tagged_partition_mass_value i)).
Qed.

(** Source for [finite_tagged_vector_quadrature_bound]: uniform
    oscillation on each original Borel cell bounds the
    error of the actual finite integral sum by that
    oscillation times the compact's measure, justifying
    the approximation in Federer 4.1.2, p. 348. *)
Theorem finite_tagged_vector_quadrature_bound (F:X->Y) y eta:
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(F x:real_norm_metric_space hNY))) y ->
  (forall x,~K x ->F x=0) ->
  (forall i x,A i x ->NY (F x-F (tag i))<=eta) ->
  NY (y-\sum_i mass i*:F (tag i))<=eta*b.
Proof.
move=>hIntegral hOff hOscillation.
pose step x:=\sum_i chi i x*:F (tag i).
have hStep:=finite_tagged_vector_sum_integral F.
have hDifference:=@total_vector_integral_subtract R X Y NY hNY mu hm F step
  y (\sum_i mass i*:F (tag i)) hIntegral hStep.
have hChiIntegral:=@measure_characteristic_integral R X mu hm K
  (fun x=>(chiK x:real_line_metric R)) (@CharacteristicFunction.laws R X K) hKMeas.
rewrite hMass in hChiIntegral.
have hMajorant:=@real_total_integral_scale R X mu hm chiK b eta hChiIntegral.
apply:(@total_vector_integral_dominated_norm R X Y NY hNY mu hm (fun x=>F x-step x)
  (y-\sum_i mass i*:F (tag i)) (fun x=>eta*chiK x) (eta*b) hDifference hMajorant)=>x.
case:(pselect (K x))=>hx.
- have[i hi]:=@finite_tagged_partition_cover R X K mesh I A tag hPart x hx.
  rewrite /step (finite_tagged_step_on_cell F hi)
    (characteristic_on_set (@CharacteristicFunction.laws R X K) hx) mulr1.
  exact:hOscillation i x hi.
- rewrite (hOff x hx) /step (finite_tagged_step_off_compact F hx) subrr
    (real_seminorm_zero hNY.1)
    (characteristic_off_set (@CharacteristicFunction.laws R X K) hx) mulr0.
  exact:lexx.
Qed.
End FiniteTaggedVectorIntegral.
