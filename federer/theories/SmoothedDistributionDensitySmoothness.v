(** Federer (1969), 4.1.2, p. 347: the
    actual distribution kernel density is of class
    infinity in the full normed dual Y*. The
    proof iterates the actual negative kernel derivatives,
    following the coordinate argument in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityOperations
  NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousDualNorm ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  TranslatedKernelTestUP TranslatedKernelTestSealed SmoothedDistributionDensityUP
  SmoothedDistributionDensityExistence SmoothedDistributionDensityContinuity SmoothedDistributionDensityDirectional
  CompactScalarKernelDirectional CoordinateClassSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothedDistributionDensitySmoothness.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Local Notation hDN := (continuous_dual_norm_is_norm hYD).

(** Source for [smoothed_distribution_density_class]: all finite
    differentiability classes of the original g_epsilon,
    Federer 4.1.2, p. 347, proved with
    actual dual-valued derivative fields and no separability
    assumption on the dual. *)
Theorem smoothed_distribution_density_class k:
  forall (psi:X->R) r (B:X->Hom Y DT) (g:X->YD),
    norm_class_all_orders hN hNS (fun _=>True) psi ->
    (forall x,r<N x ->psi x=0) ->
    @is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B ->
    is_smoothed_distribution_density B T ed g ->
    norm_class hN hDN (fun _=>True) g k.
Proof.
elim:k=>[|k IH] psi r B g hPsi hOff hB hg.
- apply:(@norm_class_zeroP R X YD N DN hN hDN (fun _=>True) g).2.
  exact:(@smoothed_distribution_density_continuous R n Y NY hNY E ev hE D hD
    psi hPsi r hOff B hB T hT YD ed DN hYD g hg).
- have[theta hTheta]:=choice (fun i:'I_n=>
    @compact_scalar_kernel_directional_exists R n psi r (@coordinate_basis R n i) hPsi hOff).
  have[G hG]:=choice hTheta.
  pose CTest i:=@TranslatedKernelTest.value R n Y NY hNY E ev hE
    (theta i) (hG i).1 r (hG i).2.1.
  have hCTest i:=@TranslatedKernelTest.laws R n Y NY hNY E ev hE
    (theta i) (hG i).1 r (hG i).2.1.
  have hFor i:exists q:X->YD,is_smoothed_distribution_density (CTest i) T ed q.
    exact:(@smoothed_distribution_density_exists R n Y NY hNY E ev hE D hD
      (theta i) (hG i).1 r (hG i).2.1 (CTest i) (hCTest i) T hT YD ed DN hYD).
  have[q hq]:=choice hFor.
  apply:(@norm_class_successor_coordinate_fields R n YD DN hDN g (fun i a=> -q i a) k).
  + exact:(@smoothed_distribution_density_continuous R n Y NY hNY E ev hE D hD
      psi hPsi r hOff B hB T hT YD ed DN hYD g hg).
  + move=>a i.
    exact:(@smoothed_distribution_density_directional R n Y NY hNY E ev hE D hD
      psi hPsi r hOff B hB T hT YD ed DN hYD g hg (@coordinate_basis R n i)
      (theta i) (G i) (hG i).2.2.1 (hG i).2.2.2 (hG i).2.1
      (CTest i) (hCTest i) (q i) (hq i) a).
  + move=>i.
    have hClass:=IH (theta i) r (CTest i) (q i) (hG i).1 (hG i).2.1 (hCTest i) (hq i).
    have hScaled:=@norm_class_scale R X YD N DN hN hDN (fun _=>True) (q i) (-1) k hClass.
    have hFun:(fun x:X=>(-1:R)*:q i x)=(fun x=> -q i x).
      apply:funext=>x; by rewrite scaleN1r.
    by rewrite hFun in hScaled.
Qed.

(** Source for [smoothed_distribution_density_smooth]: the complete
    original class-infinity assertion for g_epsilon in
    Federer 4.1.2, p. 347. Every value
    is the actual kernel-test pairing with T. *)
Theorem smoothed_distribution_density_smooth (psi:X->R) r (B:X->Hom Y DT) (g:X->YD):
  norm_class_all_orders hN hNS (fun _=>True) psi ->
  (forall x,r<N x ->psi x=0) ->
  @is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B ->
  is_smoothed_distribution_density B T ed g ->
  norm_class_all_orders hN hDN (fun _=>True) g.
Proof.
move=>hPsi hOff hB hg k.
exact:(smoothed_distribution_density_class k hPsi hOff hB hg).
Qed.
End SmoothedDistributionDensitySmoothness.
