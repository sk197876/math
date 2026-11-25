(** Federer (1969), 4.1.7, p. 358:
    every class-one form admits actual
    compact smooth tests converging together with
    their exterior derivatives near a prescribed
    compact set. The proof localises with
    the original cutoff and reuses the
    regularisation and input differential laws of
    4.1.2, pp. 346–347. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  NormHigherDifferentialFirst ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  SmoothCompactSet SmoothCompactDomainInclusion SmoothTestSpaces SmoothTestEvaluation
  CompactContinuousSmoothingTests SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP
  ExteriorDerivativeUP ExteriorDifferentialUP CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentSpaces CurrentClassOneCutoff CurrentClassOneSmoothingUniform CurrentExteriorDifferentialMap
  SmoothCurrentExteriorDerivative CurrentTestExteriorDerivative CurrentOpenRestriction
  CurrentOpenRestrictionBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneTestApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation next := (@current_test_value R h2 n U hU m.+1).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation EWhole := (@current_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation hWhole := (fun j=>@current_smooth_space_laws R h2 n (fun _=>True) hFull j).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation fv := (@current_smooth_value R h2 n (fun _=>True) hFull m.+1).
Local Notation dWhole := (@smooth_current_exterior_derivative R h2 n m (fun _=>True) hFull).
Local Notation extend := (fun j=>@current_open_test_extension R h2 n j U (fun _=>True)
  hU hFull (fun _ _=>Logic.I)).
Local Notation kernel := (@SmoothingKernel.value R n).
Local Notation family := (@SmoothingDilation.value R n kernel).

(** Source for [current_class_one_test_approximation]:
    actual compact smooth forms and their
    actual exterior derivatives approximate phi
    and d phi uniformly on K,
    supporting the unrestricted boundary equation
    of Federer 4.1.7, p. 358.
    K may be empty, and phi
    retains its original arbitrary open domain. *)
Theorem current_class_one_test_approximation (K:smooth_compact_set hNX U)
    (phi:X->Y) (beta:X->Z):
  norm_class hNX hNY U phi 1%N->
  (forall x,U x->has_exterior_derivative NX NY U phi x (beta x))->
  exists P:R->DT,forall eta:R,0<eta->exists delta:R,0<delta /\
    forall e,0<e->e<delta->forall x,smooth_compact_carrier K x->
      NY (value (P e) x-phi x)<eta /\ NZ (next (d (P e)) x-beta x)<eta.
Proof.
move=>hClass hBeta.
have [C [psi [b [hPsi [hB [hExterior [hOff [W [hW [hKW [hWU hAgreement]]]]]]]]]]]:=
  @current_class_one_compact_replacement R h2 n m U hU K phi beta hClass hBeta.
have [r [hr [C' [P [hConvolution hUniform]]]]]:=
  @compact_continuous_smoothing_tests R n Y NY hNY (@current_form_complete R h2 n m)
    U hU (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m)
    hE kernel (@SmoothingKernel.laws R n) family (@SmoothingDilation.laws R n kernel)
    C psi (norm_class_continuous hPsi) (fun x hx=>(hOff x hx).1).
pose g:R->EWhole:=fun e=>smooth_test_inclusion (hWhole m) (extend m (P e)).
have hG e:ev (g e)=value (P e).
  apply:funext=>x.
  exact:(@current_open_test_extension_values R h2 n m U (fun _=>True) hU hFull
    (fun _ _=>Logic.I) (P e) x).
have hDG e x:fv (dWhole (g e)) x=next (d (P e)) x.
  rewrite -(@current_test_exterior_derivative_inclusion R h2 n m
    (fun _=>True) hFull (extend m (P e))).
  change (@current_test_value R h2 n (fun _=>True) hFull m.+1
    (@current_test_exterior_derivative R h2 n m (fun _=>True) hFull (extend m (P e))) x=
    next (d (P e)) x).
  rewrite -(@current_open_test_exterior_commutes R h2 n m U (fun _=>True) hU hFull
    (fun _ _=>Logic.I) (P e)).
  exact:current_open_test_extension_values.
have [_ [df [hActual hDfContinuous]]]:=hPsi.
have hDifferential x:L (df x)=b x.
  apply:(exterior_derivative_unique hNX hNY _ (hExterior x)).
  exists (@continuous_multilinear_one_operator R X Y (J 1%N) NX NY
    (@ej 1%N) (@JN 1%N) (hJ 1%N) (df x));split.
  - exact:((@norm_higher_differential_first R X Y NX NY hNX hNY J ej JN hJ
      (fun _=>True) psi x (df x)).1 (hActual x Logic.I)).
  - exact:current_exterior_differential_map_values.
have hSmoothConvolution e (he:0<e) (her:e<r):
    is_smoothing_convolution hNY (family e) psi (ev (g e)).
  rewrite hG;exact:(hConvolution e he her).1.
pose KWhole:=smooth_compact_domain_inclusion (fun (x:X) (_:U x)=>Logic.I) K.
exists P=>eta hEta.
have [delta [hDelta [hDeltaR hApprox]]]:=@current_class_one_smoothing_uniform R h2 n m
  r psi df g hr hPsi (fun x=>hActual x Logic.I) hSmoothConvolution KWhole eta hEta.
exists delta;split=>// e he hed x hx.
have hA:=hApprox e he hed x hx.
have [hPhi hBetaPoint]:=hAgreement x (hKW x hx).
rewrite hG hDifferential hDG hPhi hBetaPoint in hA;exact:hA.
Qed.
End CurrentClassOneTestApproximation.
