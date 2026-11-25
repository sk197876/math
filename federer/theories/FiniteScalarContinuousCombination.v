(** Federer (1969), 4.1.7, p. 359:
    finite coordinate combinations of Baire
    coefficients and smooth pulled-back generators
    are measurable and bounded on compact
    sets. This supporting estimate uses the
    earlier measurable operations of 2.3.8,
    pp. 78–79, and compact maxima. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity VectorDaniellHypotheses
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasurableIdentityCriterion
  MeasurableTotalBasic BorelFunctionBasic MeasurableScalarVectorProduct MeasurableNormedFunctionUP
  MeasurableNormedBasic MeasurableTotalNormedArithmetic SeparableTargetNormedMeasurability CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteScalarContinuousCombination.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable d:nat.
Variable a:'I_d->X->R.
Variable b:'I_d->X->Y.
Hypothesis hContinuous:forall i,continuous (fun x=>(b i x:real_norm_metric_space hNY)).
Arguments hContinuous : clear implicits.

(** Source for [finite_scalar_continuous_combination_measurable]:
    the original finite coordinate sum is
    norm-measurable, supporting the Baire pullback
    in Federer 4.1.7, p. 359.
    Neither the source measure nor the
    generators need have finite total mass
    or compact support. *)
Theorem finite_scalar_continuous_combination_measurable
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu):
  (forall i,is_measure_measurable_function mu
    (partial_function_total (fun x=>(a i x:real_line_metric R))))->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(\sum_i a i x*:b i x:real_norm_metric_space hNY))).
Proof.
move=>hA.
have [C [hCount hDense]]:=hSep.
have hIdentity:=(@measurable_identity_iff_open_sets R X mu hm).2 (radon_open_measurable hr).
have hEach i:is_measurable_normed_function mu
    (partial_function_total (fun x=>(a i x*:b i x:real_norm_metric_space hNY))).
  apply:(@separable_target_measurable_normed R X Y NY hNY C mu hm _ hCount hDense).
  have hB:=@measurable_total_borel_postcomposition R X X (real_norm_metric_space hNY)
    mu hm id (fun x=>(b i x:real_norm_metric_space hNY)) hIdentity
    (continuous_borel_function (hContinuous i)).
  exact:(@measurable_scalar_vector_product R X Y NY hNY mu hm (a i) (b i) hSep (hA i) hB).
have hSum (s:seq 'I_d):is_measurable_normed_function mu
    (partial_function_total (fun x=>(\sum_(i<-s) a i x*:b i x:real_norm_metric_space hNY))).
  elim:s=>[|i s ih].
  - have hZero:(fun x:X=>(\sum_(i<-([::]:seq 'I_d)) a i x*:b i x:Y))=(fun _:X=>(0:Y)).
      apply:funext=>x;exact:big_nil.
    rewrite hZero.
    exact (@measurable_normed_total_constant R X Y NY hNY mu hm 0).
  - have hCons:(fun x:X=>(\sum_(j<-i::s) a j x*:b j x:Y))=
        (fun x=>a i x*:b i x+\sum_(j<-s) a j x*:b j x).
      apply:funext=>x;exact:big_cons.
    rewrite hCons.
    exact:(@measurable_normed_total_add R X Y NY hNY mu hm _ _ (hEach i) ih).
exact ((hSum (index_enum 'I_d)).1).
Qed.

(** Source for [finite_scalar_continuous_combination_compact_bound]:
    globally bounded original scalar coefficients
    give a finite norm bound on
    every compact source set, supporting
    Federer 4.1.7, p. 359. The
    actual coordinate sum is retained. *)
Theorem finite_scalar_continuous_combination_compact_bound (M:'I_d->R):
  (forall i,0<=M i)->(forall i x,`|a i x|<=M i)->
  forall K:set X,compact K->exists B:R,0<=B /\
    forall x,K x->NY (\sum_i a i x*:b i x)<=B.
Proof.
move=>hM hA K hK.
have hEach i:exists B:R,0<=B /\forall x,K x->NY (b i x)<=B.
  case:(pselect (K !=set0))=>hNonempty.
  - have hNorm:continuous (fun x:X=>(NY (b i x):real_line_metric R)).
      move=>x;exact:(continuous_comp (hContinuous i x)
        (@real_norm_metric_norm_continuous R Y NY hNY (b i x))).
    have [x [hx hMax]]:=@continuous_compact_maximum R X K (fun x=>NY (b i x)) hNonempty hK hNorm.
    exists (NY (b i x));split;first exact:real_seminorm_nonnegative hNY.1 _.
    exact:hMax.
  - exists 0;split;first exact:lexx.
    move=>x hx;exact:False_ind _ (hNonempty (ex_intro _ x hx)).
have [B hB]:=choice hEach.
exists (\sum_i M i*B i);split.
- apply:sumr_ge0=>i _;exact:(mulr_ge0 (hM i) (hB i).1).
- move=>x hx;apply:le_trans (real_seminorm_sum hNY.1 _) _.
  apply:ler_sum=>i _;rewrite (real_seminorm_scale hNY.1).
  apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative hNY.1 (b i x)) (hA i x))).
  exact:(ler_wpM2l (hM i) ((hB i).2 x hx)).
Qed.
End FiniteScalarContinuousCombination.
