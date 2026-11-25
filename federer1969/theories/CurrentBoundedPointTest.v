(** Federer (1969), 4.1.12, p. 368: bounded
    smooth tests isolate finitely many original endpoints.
    Prove the supporting point-test existence from the
    original radial bump of 3.1.13, p. 224,
    its actual smoothness and the preceding scalar
    compact-function realization. The construction serves existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  InnerSmoothUnitBump NormUnitBumpSealed NormScaledUnitBump ContinuousMultilinearSealed FiniteNormEquivalence
  CurrentSpaces CurrentSupportGeometry CurrentZeroCovectorMaps CurrentScalarCompactFunction
  AlternatingZero SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBoundedPointTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation DT := (@current_test_space R h2 n Full hFull 0%N).
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation ev := (fun k=>@ContinuousMultilinear.evaluation R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).

(** Source for [current_bounded_point_test_exists]: at
    every source point and positive radius r there
    is an original scalar test gamma, with values
    in [0,1], gamma(center)=1 and support inside the
    closed ball of radius 2r. This supports the
    infinite-mass witness in Federer 4.1.12, p. 368,
    by the actual radial bump of 3.1.13,
    p. 224. Dimension zero is included. *)
Theorem current_bounded_point_test_exists (center:X) (r:R):
  0<r->exists gamma:DT,
    (@current_test_support R h2 n 0%N Full hFull gamma `<=` [set y|NX (y-center)<=2*r]) /\
    (forall y,0<=@current_zero_form_coefficient R n
      (@current_test_value R h2 n Full hFull 0%N gamma y)<=1) /\
    @current_test_value R h2 n Full hFull 0%N gamma center=@zero_form R X R^o 1.
Proof.
move=>hr.
pose mu:=inner_smooth_unit_bump (@euclidean_inner_productP R n).
pose hMu:=inner_smooth_unit_bump_laws (@euclidean_inner_productP R n).
pose beta:=norm_scaled_unit_bump mu center r.
pose hSquared:=inner_product_squared_norm_specification (@euclidean_inner_productP R n).
have hBase:norm_class_all_orders hNX hAbs Full mu.
  exact:(@NormUnitBump.smooth R X NX (@euclidean_inner_product R n) hNX hSquared Z ev ZN hZ).
have hSmooth:norm_class_all_orders hNX hAbs Full beta.
  exact:(@norm_scaled_unit_bump_smooth R X NX hNX mu center r Z ev ZN hZ hBase).
pose K:=@Build_smooth_compact_set R X NX hNX Full [set y|NX (y-center)<=2*r]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) NX hNX center (2*r)).
have hOff y:~smooth_compact_carrier K y->beta y=0.
  move=>hy;apply:(norm_scaled_unit_bump_outer hNX hMu hr).
  apply:ltW;rewrite ltNge;exact/negP.
have[gamma [hValue hSupport]]:=@current_scalar_compact_function_exists R h2 n Full hFull K beta hSmooth hOff.
exists gamma;split;first exact:hSupport.
split.
- move=>y;rewrite (hValue y Logic.I).
  change (is_true (0<=zero_form_value (@zero_form R X R^o (beta y))<=1)).
  rewrite zero_formK;exact:(norm_scaled_unit_bump_range hMu center r y).
- rewrite (hValue center Logic.I).
  have hOne:beta center= 1.
    apply:(norm_scaled_unit_bump_inner hNX hMu hr).
    by rewrite subrr (real_seminorm_zero hNX.1);exact:ltW hr.
  by rewrite hOne.
Qed.
End CurrentBoundedPointTest.
