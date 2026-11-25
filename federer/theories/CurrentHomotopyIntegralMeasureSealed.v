(** Federer (1969), 4.1.9, p. 363: the original
    integral of weighted slice image measures. Its
    independent specification uses Radon laws and the
    literal time integrals of positive compact scalar
    tests. The weighted product image proves existence;
    downstream variation bounds use the opaque public law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentHomotopyUP
  CurrentIntegrationCriterion CurrentHomotopySliceMeasureIntegral CurrentHomotopyCylinder
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP
  CurrentHomotopyTimePartialIntegral RadonCompactScalarIntegral RadonPositiveCompactUniqueness CurrentHomotopyIntegralMeasureUP CurrentHomotopyIntegralMeasureExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentHomotopyIntegralMeasureSignature.
(** Source for [value]: the opaque original integral
    of weighted slice image measures in Federer
    4.1.9, p. 363. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_integration_representable_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),set (current_domain R nu V)->\bar R.
(** Source for [laws]: only the independent original
    Radon and scalar-test integral laws are exposed,
    supporting Federer 4.1.9, p. 363. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_integration_representable_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),
  @is_current_homotopy_integral_measure R h2 n nu j A U V f g h hHomotopy T hT
    (@value R h2 n nu j A U V f g h hHomotopy T hT hProper).
End CurrentHomotopyIntegralMeasureSignature.
Module CurrentHomotopyIntegralMeasure:CurrentHomotopyIntegralMeasureSignature.
(** Source for [value]: seal the independently proved
    integral-measure witness supporting Federer 4.1.9,
    p. 363. No construction is exposed. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_integration_representable_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):set (current_domain R nu V)->\bar R:=
  projT1 (cid (@current_homotopy_integral_measure_exists R h2 n nu j A U V f g h hHomotopy T hT hProper)).
(** Source for [laws]: the opaque witness satisfies
    its independent original specification, supporting
    Federer 4.1.9, p. 363. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_integration_representable_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):
  @is_current_homotopy_integral_measure R h2 n nu j A U V f g h hHomotopy T hT
    (@value R h2 n nu j A U V f g h hHomotopy T hT hProper).
Proof.
exact:(projT2 (cid (@current_homotopy_integral_measure_exists R h2 n nu j A U V f g h hHomotopy T hT hProper))).
Qed.
End CurrentHomotopyIntegralMeasure.
