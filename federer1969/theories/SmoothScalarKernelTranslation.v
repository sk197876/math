(** Federer (1969), 4.1.2, p. 347: the
    scalar kernel z |-> psi(x-z) is smooth
    and measurable for every centre x. The already
    proved affine-dilation calculus supplies its smoothness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ContinuousMultilinearSealed NormRegularity NormClassHigherUP NormAffineDilationDifferentials
  PartialFunctionBasic MeasureUP MeasurableFunctionUP EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  NormClassZeroTotalMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section KernelTranslation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.

(** Source for [smooth_scalar_kernel_translation]: the original
    scalar convolution kernel is smooth in its integration
    variable, supporting Federer 4.1.2, p. 347. *)
Theorem smooth_scalar_kernel_translation x:
  norm_class_all_orders hN hR (fun _=>True) (fun z=>psi (x-z)).
Proof.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR.
have h:=@norm_class_infinity_affine_dilation R X R^o N (fun t:R^o=>`|t|) hN hR
  Z ev ZN hZ psi (-1) x hPsi.
have hEq:(fun z:X=>psi ((-1:R)*:z+x))=(fun z=>psi (x-z)).
  apply:funext=>z; by rewrite scaleN1r addrC.
rewrite hEq in h; exact h.
Qed.

(** Source for [smooth_scalar_kernel_translation_measurable]: the
    original scalar kernel is measurable for actual Lebesgue
    measure before choosing its integral, supporting
    Federer 4.1.2, p. 347. *)
Theorem smooth_scalar_kernel_translation_measurable x:
  is_measure_measurable_function (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(psi (x-z):real_line_metric R))).
Proof.
exact:(@norm_class_zero_scalar_real_measurable R X N hN (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_open R n)
  (fun z=>psi (x-z)) (norm_class_continuous (smooth_scalar_kernel_translation x 0%N))).
Qed.
End KernelTranslation.
