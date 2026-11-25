(** Federer (1969), 4.1.2, p. 347: the original directional
    derivative of a Lipschitz field has a measurable bounded total
    representative on its conull domain. Its values on every point
    of the original derivative graph are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormedCurveDerivativeUP NormedDerivativeBounds NormDirectionalQuotientContinuity
  NormClassZeroWhole NormClassZeroTotalMeasurable PuncturedNormReciprocalSequence
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP MeasurableFunctionUP MeasurablePartialLimits
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormDirectionalMeasurableRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable f:X->Y.

Variable v:X.
Local Notation Der := (fun x w=>punctured_norm_limit NY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w).
Hypothesis hF:continuous (f:real_norm_metric_space hN->real_norm_metric_space hNY).
Hypothesis hExists:measure_almost_everywhere mu [set x|exists w,Der x w].

(** Source for [norm_directional_measurable_representative_exists]:
    the original D_v f has a measurable total representative
    preserving every actual derivative value and zero off its
    domain, supporting Federer 4.1.2, p. 347.
    Actual conull existence is proved separately from reflexivity. *)
Theorem norm_directional_measurable_representative_exists:
  exists xi:X->Y,
    (forall x w,Der x w ->xi x=w) /\
    (forall x,~(exists w,Der x w) ->xi x=0) /\
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:real_norm_metric_space hNY))) /\
    measure_almost_everywhere mu [set x|Der x (xi x)].
Proof.
have hFor x:exists z:Y,(forall w,Der x w ->z=w) /\
    (~(exists w,Der x w) ->z=0).
  case:(pselect (exists w,Der x w))=>[[w hw]|hn].
  - exists w; split.
    + move=>z hz; exact:(@punctured_norm_limit_unique R Y NY hNY
        (fun t=>t^-1*:(f (x+t*:v)-f x)) w z hw hz).
    + by move=>h; exfalso; apply:h; exists w.
  - exists 0; split; last by move=>_.
    by move=>w hw; exfalso; apply:hn; exists w.
have[xi hXi]:=choice hFor.
have hAE:measure_almost_everywhere mu [set x|Der x (xi x)].
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hExists).
  move=>x [w hw].
  change (Der x (xi x)).
  have hValue:xi x=w:=(hXi x).1 w hw.
  by rewrite hValue.
pose Q m x:=((((m.+1)%:R:R)^-1)^-1)*:(f (x+(((m.+1)%:R:R)^-1)*:v)-f x).
have hQM m:is_measure_measurable_function mu
    (partial_function_total (fun x=>(Q m x:real_norm_metric_space hNY))).
  have hContinuous:=@norm_directional_quotient_continuous R X Y N NY hN hNY f v hF
    (((m.+1)%:R:R)^-1).
  exact:(@norm_class_zero_total_measurable R X Y N NY hN hNY mu hm
    (@euclidean_distribution_measure_open R n) (Q m)
    (norm_continuous_whole_class_zero hContinuous)).
have hLimit:measure_almost_everywhere mu
    (partial_function_limit_locus
      (fun m=>partial_function_total (fun x=>(Q m x:real_norm_metric_space hNY)))
      (partial_function_total (fun x=>(xi x:real_norm_metric_space hNY)))).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAE).
  move=>x hx; exists (fun m=>(Q m x:real_norm_metric_space hNY)),(xi x:real_norm_metric_space hNY).
  split; first by move=>m.
  split; first reflexivity.
  exact:(@punctured_norm_reciprocal_sequence R Y NY hNY _ (xi x) hx).
have hMeas:=@measurable_partial_functions_almost_limit R X (real_norm_metric_space hNY)
  mu hm _ _ hQM hLimit.
exists xi; split; first by move=>x; exact:(hXi x).1.
split; first by move=>x; exact:(hXi x).2.
by split.
Qed.
End NormDirectionalMeasurableRepresentative.
