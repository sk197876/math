(** Federer (1969), 3.2.5(3), p. 245: the
    image of each measurable relative inverse image is
    Hausdorff measurable. Hence the weight restricted to the
    represented image is measurable, using 3.2.4. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureFiniteClosure MeasureAlmostBasic MeasurableFunctionUP LipschitzUP HausdorffMeasure
  LipschitzMeasurableImages MeasurableRelativeZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_represented_weight_measurable]: the open-set
    test using W and f(W) in the last paragraph of
    Federer 3.2.5, p. 245. The target cutoff is
    specified by the opaque zero-extension graph. *)
Theorem lipschitz_represented_weight_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) B
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) B ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (partial_function_zero_extension (0:real_line_metric R) B (partial_function_total (fun x=>g (f x)))) ->
  is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_zero_extension (0:real_line_metric R) (f @` B) (partial_function_total g)).
Proof.
move=>hLip hB hSource.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R Y m.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R Y m.
apply:(@measurable_relative_zero_extension R Y [the topologicalType of real_line_metric R]
  beta hb 0 (f @` B) (partial_function_total g)).
- exact (euclidean_lipschitz_measurable_image hLip hB).
- rewrite partial_function_total_domain; exact (measure_almost_everywhere_true hb).
- move=>U hU.
  pose T:=partial_function_preimage (partial_function_total g) U.
  pose W:=B `&` (f @^-1` T).
  have hW:measure_measurable mu W.
    have hMeas:=measure_measurable_intersection hm hB (measurable_function_open_preimage hSource hU).
    have hEq:W=B `&` partial_function_preimage
      (partial_function_zero_extension (0:real_line_metric R) B (partial_function_total (fun x=>g (f x)))) U.
      apply/seteqP; split=>x.
      + move=>[hx [z [hz hUz]]]; split=>//; exists z; split=>//.
        apply:(partial_function_zero_extension_on _ _ _ hx).2; exact hz.
      + move=>[hx [z [hz hUz]]]; split=>//; exists z; split=>//.
        exact ((partial_function_zero_extension_on _ _ _ hx).1 hz).
    by rewrite hEq.
  have hImage:=euclidean_lipschitz_measurable_image hLip hW.
  have hEq:(f @` B) `&` T=f @` W.
    apply/seteqP; split=>y.
    + move=>[[x hx hxy] hTy]; exists x.
      * split; first exact hx.
        change (T (f x)); by rewrite hxy.
      * exact hxy.
    + move=>[x [hx hTx] hxy]; split; first by exists x.
      by rewrite -hxy.
  by rewrite hEq.
Qed.
