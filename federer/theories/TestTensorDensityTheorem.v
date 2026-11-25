(** Federer (1969), 4.1.3, p. 348: the canonical image of
    [tensor_n D(R,R)] tensor Y is dense in D(R^n,Y), with
    its literal final topology. The actual separated kernel,
    finite Borel sums and smoothing limit close every premise.
    The Banach target need not be separable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom TensorUP TensorFamilyUP RealNormUP NormMetric CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothingKernelUP SmoothingDilationSealed SmoothSmoothingFamilyUP TestSmoothingFamilyUP
  TestSmoothingFamilyExistence ContinuousSmoothSmoothingExistence ContinuousTestSmoothingConvergence
  SeparatedKernelSealed TestTensorMapUP TestTensorMapExistence TensorSmoothingClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TestTensorDensityTheorem.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Local Notation D1 := (smooth_test_space hA).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y N NY hN hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable T W:lmodType R.
Variable mu:{dffun forall i:'I_n,D1}->T.
Variable nu:T->Y->W.

(** Source for [test_tensor_map_dense]: every original test
    neighbourhood meets the actual canonical tensor image,
    Federer 4.1.3, p. 348. This quantifies over all original
    neighbourhoods, without replacing the literal topology by
    its locally convex counterpart. *)
Theorem test_tensor_map_dense (F:Hom W DT):
  is_test_tensor_map hA hE mu nu F ->
  forall f:DT,forall V,smooth_test_opens hE hD V ->V f ->
    exists w:W,V (F w).
Proof.
move=>hF f V hV hf.
pose gamma:=@SeparatedKernel.factor R n A av hA.
pose phi:=fun x:X=>\prod_i smooth_test_value hA gamma (x i).
have hPhi:=@SeparatedKernel.laws R n A av hA.
pose family:=@SmoothingDilation.value R n phi.
have hFamily:=@SmoothingDilation.laws R n phi.
have[P hP]:=@continuous_smooth_smoothing_family_exists R n Y NY hNY hY
  E ev hE phi hPhi family hFamily.
have[Q hQ]:=@test_smoothing_family_exists R n Y NY hNY E ev hE
  phi hPhi family hFamily P hP.
have[d [hd hLimit]]:=@continuous_test_smoothing_neighbourhood_limit R n Y NY hNY hY
  E ev hE D hD phi hPhi family hFamily P hP Q hQ f V hV hf.
have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
have hSmall:d/2<d by rewrite ltr_pdivrMr ?ltr0n //; lra.
have hPoint:V (Q (d/2) f):=hLimit (d/2) hHalf hSmall.
exact:(@tensor_smoothing_in_image_closure R n A av hA gamma hPhi family hFamily
  Y NY hNY hY E ev hE D hD T W mu nu F hF P hP Q hQ f (d/2) hHalf V hV hPoint).
Qed.

(** Source for [test_tensor_dense_map_exists]: the complete
    original assertion of Federer 4.1.3, p. 348. Independently
    specified family and binary tensor products have an actual
    canonical map with dense image in the actual test space. *)
Theorem test_tensor_dense_map_exists:
  is_tensor_product_family mu ->is_tensor_product nu ->
  exists F:Hom W DT,is_test_tensor_map hA hE mu nu F /\
    forall f:DT,forall V,smooth_test_opens hE hD V ->V f ->
      exists w:W,V (F w).
Proof.
move=>hT hW.
have[F hF]:=@test_tensor_map_exists R n A av hA Y NY hNY E ev hE T W mu nu hT hW.
exists F; split; first exact hF.
exact:(test_tensor_map_dense hF).
Qed.
End TestTensorDensityTheorem.
