(** Federer (1969), 4.1.12, p. 369: a
    translated cutoff on (u,u+4q), q>0,
    has value one at u+2q,
    range [0,1] and derivative comass at
    most q^(-1). For q=k^(-3)
    this is exactly the printed phi_k.
    Reuse the opaque unit cutoff and affine calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate InnerNorm HilbertFormCompactness
  ContinuousMultilinearSealed NormScaledUnitBump CurrentSpaces CurrentSupportGeometry CurrentCoefficientNorms
  AlternatingForms AlternatingZero CurrentZeroCovectorMaps SmoothCompactSet SmoothTestSpaces
  CurrentScalarCompactFunction CurrentUnitIntervalCutoffUP CurrentUnitIntervalCutoffSealed
  CurrentTestExteriorDerivative CurrentScalarExteriorLipschitzBound ScalarCurrentIntervalCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScaledIntervalCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation ev := (fun k=>@ContinuousMultilinear.evaluation R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X R^o NX (fun t:R^o=>`|t|) hNX hAbs).

(** Source for [current_scaled_interval_cutoff_exists]:
    the actual smooth compact scalar test
    required for the original phi_k exists
    with the exact support, unit value
    and derivative constant, Federer 4.1.12,
    p. 369. The scale q
    is any positive real number. *)
Theorem current_scaled_interval_cutoff_exists (u q:R):0<q->
  exists gamma:DT,
    (@current_test_support R h2 1%N 0%N Full hFull gamma `<=`
      [set x|u<euclidean_one_project x<u+4*q]) /\
    (forall x,0<=@current_zero_form_coefficient R 1%N (value gamma x)<=1) /\
    value gamma (euclidean_one_embed (u+2*q))=@zero_form R X R^o 1 /\
    forall x,@current_form_comass R h2 1%N 1%N
      (@current_test_value R h2 1%N Full hFull 1%N
        (@current_test_exterior_derivative R h2 1%N 0%N Full hFull gamma) x)<=q^-1.
Proof.
move=>hq.
have hq0:q!=0 by rewrite gt_eqF.
have hInverse:0<q^-1 by rewrite invr_gt0.
pose eta:=@CurrentUnitIntervalCutoff.value R.
have[hEta [hRange [hLip [hTwo hOff]]]]:=@CurrentUnitIntervalCutoff.laws R.
pose beta:=norm_scaled_unit_bump eta (euclidean_one_embed u) q.
have hSmooth:norm_class_all_orders hNX hAbs Full beta.
  exact:(@norm_scaled_unit_bump_smooth R X NX hNX eta (euclidean_one_embed u) q Z ev ZN hZ hEta).
pose K:=scalar_current_compact_interval R (u+q/4) (u+15*q/4).
have hCoordinate x:euclidean_one_project (q^-1*:(x-euclidean_one_embed u))=
    (euclidean_one_project x-u)/q.
  by rewrite /euclidean_one_project /euclidean_one_embed !ffunE mulrC.
have hZero x:~smooth_compact_carrier K x->beta x=0.
  move=>hx;apply:hOff=>hBounds;apply:hx.
  rewrite hCoordinate in hBounds.
  have hL:=ler_wpM2r (ltW hq) (andP hBounds).1.
  have hH:=ler_wpM2r (ltW hq) (andP hBounds).2.
  rewrite divfK // in hL hH.
  rewrite scalar_current_compact_interval_carrier;apply/andP;split;lra.
have[gamma [hValue hSupport]]:=@current_scalar_compact_function_exists R h2 1%N Full hFull K beta hSmooth hZero.
have hCoefficient x:@current_zero_form_coefficient R 1%N (value gamma x)=beta x.
  rewrite (hValue x Logic.I).
  change (zero_form_value (@zero_form R X R^o (beta x))=beta x);exact:zero_formK.
exists gamma;split.
- move=>x hx;have hBounds:=hSupport x hx.
  rewrite scalar_current_compact_interval_carrier in hBounds.
  have[hLow hHigh]:=andP hBounds;apply/andP;split;lra.
- split.
  + move=>x;rewrite hCoefficient;exact:hRange.
  + split.
    * rewrite (hValue _ Logic.I) /beta /norm_scaled_unit_bump.
      have hPoint:q^-1*:(euclidean_one_embed (u+2*q)-euclidean_one_embed u)=euclidean_one_embed 2.
        apply/ffunP=>i;rewrite /euclidean_one_embed !ffunE.
        change (q^-1*(u+2*q-u)= 2).
        field;exact:hq0.
      by rewrite hPoint /eta hTwo.
    * have hRawLip x y:`|beta x-beta y|<=q^-1*NX (x-y).
        have h:=hLip (q^-1*:(x-euclidean_one_embed u))
          (q^-1*:(y-euclidean_one_embed u)).
        have hDifference:(q^-1*:(x-euclidean_one_embed u))-
            (q^-1*:(y-euclidean_one_embed u))=q^-1*:(x-y).
          rewrite -scalerBr;congr (_*: _);by rewrite opprB addrA subrK.
        rewrite hDifference (real_seminorm_scale hNX.1) (ger0_norm (ltW hInverse)) in h.
        exact:h.
      have hActualLip x y:`|@current_zero_form_coefficient R 1%N (value gamma x)-
          @current_zero_form_coefficient R 1%N (value gamma y)|<=q^-1*NX (x-y).
        by rewrite !hCoefficient;exact:hRawLip.
      have hBound:=@current_scalar_exterior_lipschitz_bound R h2 1%N hFull
        (smooth_test_inclusion (@current_smooth_space_laws R h2 1%N Full hFull 0%N) gamma)
        q^-1 (ltW hInverse) hActualLip.
      move=>x.
      change (@current_form_comass R h2 1%N 1%N
        (@current_smooth_value R h2 1%N Full hFull 1%N
          (smooth_test_inclusion (@current_smooth_space_laws R h2 1%N Full hFull 1%N)
            (@current_test_exterior_derivative R h2 1%N 0%N Full hFull gamma)) x)<=q^-1).
      rewrite current_test_exterior_derivative_inclusion;exact:hBound x.
Qed.
End CurrentScaledIntervalCutoff.
