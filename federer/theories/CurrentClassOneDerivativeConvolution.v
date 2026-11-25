(** Federer (1969), 4.1.7, p. 358:
    regularisation of an original class-one
    form commutes with its actual first
    differential. Reuse the full input
    differential theorem of 4.1.2, p. 347,
    on the actual finite form target.
    No separability of an entire operator
    space is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces SmoothFunctionDerivativesUP
  SmoothingKernelUP SmoothingKernelSealed SmoothingDilationUP SmoothingDilationSealed
  SmoothingConvolutionUP SmoothingInputHigherDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneDerivativeConvolution.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation D := (@current_smooth_derivatives R h2 n (fun _=>True) hFull m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n (fun _=>True) hFull m).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Local Notation kernel := (@SmoothingKernel.value R n).
Local Notation family := (@SmoothingDilation.value R n kernel).

(** Source for [current_class_one_first_derivative_convolution]:
    the original first differential of
    a regularised class-one form is
    the regularisation of its original first
    differential, supporting the boundary approximation
    in Federer 4.1.7, p. 358.
    The arbitrary candidate df must be
    the actual differential field everywhere. *)
Theorem current_class_one_first_derivative_convolution e (f:X->Y) (df:X->J 1%N) (g:E):
  0<e->norm_class hNX hNY (fun _=>True) f 1%N->
  (forall x,has_norm_higher_differential NX ej JN (fun _=>True) f 1%N x (df x))->
  is_smoothing_convolution hNY (family e) f (ev g)->
  is_smoothing_convolution hN1 (family e) df (fun x=>@D 1%N x g).
Proof.
move=>he hClass hActual hConvolution.
have [a [b [hA [hB hIntegral]]]]:=@smoothing_input_higher_differential_exists R n Y NY hNY
  (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
  kernel (@SmoothingKernel.laws R n) family (@SmoothingDilation.laws R n kernel)
  e he 1%N f (ev g) hClass hConvolution.
have hInput:a=df.
  apply:funext=>x.
  exact:(norm_higher_differential_unique hNX hNY hJ (hA x) (hActual x)).
have hOutput:b=(fun x=>@D 1%N x g).
  apply:funext=>x.
  exact:(norm_higher_differential_unique hNX hNY hJ (hB x)
    (smooth_derivative_exact hD 1%N g Logic.I)).
by rewrite hInput hOutput in hIntegral.
Qed.
End CurrentClassOneDerivativeConvolution.
