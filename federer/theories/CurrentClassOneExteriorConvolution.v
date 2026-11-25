(** Federer (1969), 4.1.7, p. 358:
    exterior differentiation of a regularised
    class-one form is convolution of its
    original exterior derivative. Reuse 4.1.2,
    p. 347, and bounded linear
    alternation of the actual first differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  NormHigherDifferentialUP NormHigherDifferentialUnique NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentExteriorDifferentialMap
  SmoothCurrentExteriorDerivative CurrentClassOneDerivativeConvolution ContinuousConvolutionLinearImage
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneExteriorConvolution.
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
Local Notation hNZ := (@current_form_comass_real_norm R h2 n m.+1).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation fv := (@current_smooth_value R h2 n (fun _=>True) hFull m.+1).
Local Notation D := (@current_smooth_derivatives R h2 n (fun _=>True) hFull m).
Local Notation d := (@smooth_current_exterior_derivative R h2 n m (fun _=>True) hFull).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation kernel := (@SmoothingKernel.value R n).
Local Notation family := (@SmoothingDilation.value R n kernel).

(** Source for [current_class_one_exterior_convolution]:
    d(Phi_e*f)=Phi_e*(df) for
    an original class-one form, supporting
    the boundary formula of Federer 4.1.7,
    p. 358. Here df is
    actual alternation of the supplied genuine
    first differential, and d on the
    output is the actual smooth operator. *)
Theorem current_class_one_exterior_convolution e (f:X->Y) (df:X->J 1%N) (g:E):
  0<e->norm_class hNX hNY (fun _=>True) f 1%N->
  (forall x,has_norm_higher_differential NX ej JN (fun _=>True) f 1%N x (df x))->
  is_smoothing_convolution hNY (family e) f (ev g)->
  is_smoothing_convolution hNZ (family e) (fun x=>L (df x)) (fv (d g)).
Proof.
move=>he hClass hActual hConvolution.
have [_ [a [hA hContinuous]]]:=hClass.
have hEqual:a=df.
  apply:funext=>x;exact:(norm_higher_differential_unique hNX hNY hJ
    (hA x Logic.I) (hActual x)).
rewrite hEqual in hContinuous.
have hFirst:=@current_class_one_first_derivative_convolution R h2 n m e f df g
  he hClass hActual hConvolution.
have hImage:=@continuous_convolution_linear_image R n (J 1%N) Z (@JN 1%N) NZ hN1 hNZ
  (@current_form_complete R h2 n m.+1) df (fun x=>@D 1%N x g) (family e) e hContinuous
  (@smoothing_dilation_smooth R n kernel (@SmoothingKernel.laws R n)
    family (@SmoothingDilation.laws R n kernel) e he)
  (@smoothing_dilation_zero_beyond_radius R n kernel family (@SmoothingKernel.laws R n)
    (@SmoothingDilation.laws R n kernel) e he) L
  (@current_exterior_differential_map_bounded R h2 n m) hFirst.
have hOutput:(fun x=>L (@D 1%N x g))=fv (d g).
  apply:funext=>x;exact:esym (@smooth_current_exterior_derivative_values R h2 n m
    (fun _=>True) hFull g x Logic.I).
by rewrite hOutput in hImage.
Qed.
End CurrentClassOneExteriorConvolution.
