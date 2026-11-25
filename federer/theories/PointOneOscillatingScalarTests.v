(** Federer (1969), 4.1.15, p. 373: the actual
    compactly supported smooth example maps are scalar
    original test functions under the existing R=R^1
    identification. This preserves the printed D^0(R)
    hypothesis, rather than merely using arbitrary smooth
    maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityLinearMaps InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanScalarCoordinateMaps EuclideanOneCoordinate
  AlternatingForms AlternatingZero CurrentSpaces CurrentCoefficientNorms
  CurrentZeroCovectorMaps SmoothFunctionSpaceUP SmoothCompactSet
  FiniteNormMetricCompactness SmoothTestSpaces SmoothTestRealisation
  PointOneOscillatingMapsUP PointOneOscillatingMapsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointOneOscillatingScalarTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o 0%N).
Local Notation NY:=(@current_form_comass R h2 1%N 0%N).
Local Notation hNY:=(@current_form_comass_real_norm R h2 1%N 0%N).
Local Notation E:=(@current_smooth_space R h2 1%N Full hFull 0%N).
Local Notation ev:=(@current_smooth_value R h2 1%N Full hFull 0%N).
Local Notation hE:=(@current_smooth_space_laws R h2 1%N Full hFull 0%N).
Local Notation DT:=(@current_test_space R h2 1%N Full hFull 0%N).
Local Notation value:=(@current_test_value R h2 1%N Full hFull 0%N).
Local Notation u:=(@PointOneOscillatingMaps.value R).
Local Notation hU:=(@PointOneOscillatingMaps.laws R).
Local Notation p:=(@euclidean_scalar_coordinate_map R 1%N ord0).
Local Notation zf:=(@current_scalar_zero_form R 1%N).

(** Source for [point_one_oscillating_scalar_tests_exist]: the
    literal scalar test family of the last paragraph of
    4.1.15, p. 373. Its coefficients are exactly the
    previously specified actual oscillating maps, so all earlier
    quantitative and image laws apply to this same family. *)
Theorem point_one_oscillating_scalar_tests_exist:
  exists psi:nat->DT,forall i x,
    zero_form_value (value (psi i) x)=euclidean_one_project (u i x).
Proof.
pose C:set (real_norm_metric_space hNX):=[set x:X|NX x<=2].
have hCompact:compact C:=@finite_norm_metric_ball_compact R X NX hNX
  1%N (@coordinate_basis R 1%N) (@coordinate_basisP R 1%N) 2.
pose K:=@Build_smooth_compact_set R X NX hNX Full C
  (fun _ _=>Logic.I) hCompact.
have hOne:forall i,exists psi:DT,forall x,
    zero_form_value (value psi x)=euclidean_one_project (u i x).
  move=>i.
  have hSmooth:norm_class_all_orders hNX hNY Full (fun x:X=>zf (p (u i x))).
    move=>k.
    have hScalar:=@norm_class_postcompose_linear R X X R^o NX NX NS hNX hNX hNS
      Full (u i) p k (@euclidean_scalar_coordinate_bounded R 1%N ord0)
      (@point_one_oscillating_smooth R u hU i k).
    exact:(@norm_class_postcompose_linear R X R^o Y NX NS NY hNX hNS hNY
      Full (fun x:X=>p (u i x)) zf k
      (@current_scalar_zero_form_bounded R h2 1%N) hScalar).
  have hOff:forall x,~smooth_compact_carrier K x->zf (p (u i x))=0.
    move=>x hx.
    have hFar:2<=NX x.
      apply:ltW;by rewrite ltNge;exact/negP.
    by rewrite (@point_one_oscillating_off R u hU i x hFar) !linear0.
  have [psi hPsi]:=@smooth_test_realisation R X Y NX NY hNX hNY
    Full E ev hE K (fun x:X=>zf (p (u i x))) hSmooth hOff.
  exists psi=>x.
  change (zero_form_value (ev (smooth_test_inclusion hE psi) x)=
    euclidean_one_project (u i x)).
  rewrite (hPsi x Logic.I) zero_formK.
  by [].
exists (fun i=>projT1 (cid (hOne i)))=>i x.
exact:((projT2 (cid (hOne i))) x).
Qed.
End PointOneOscillatingScalarTests.
