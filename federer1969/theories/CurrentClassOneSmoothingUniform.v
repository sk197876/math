(** Federer (1969), 4.1.7, p. 358:
    actual regularisation of a class-one
    form converges together with its exterior
    derivative on each original compact set.
    Both limits follow from the already
    proved continuous convolution approximation and
    the original first-differential commutation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  NormHigherDifferentialUP NormHigherDifferentialUnique NormClassOneUP NormClassZeroPostcompose
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentExteriorDifferentialMap
  SmoothCompactSet SmoothCurrentExteriorDerivative CurrentClassOneExteriorConvolution
  SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP ContinuousSmoothingEventualUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentClassOneSmoothingUniform.
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
Local Notation d := (@smooth_current_exterior_derivative R h2 n m (fun _=>True) hFull).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation kernel := (@SmoothingKernel.value R n).
Local Notation family := (@SmoothingDilation.value R n kernel).

(** Source for [current_class_one_smoothing_uniform]:
    regularisation converges simultaneously to
    the original class-one form and its
    actual exterior derivative on each compact
    index, supporting the boundary identity
    of Federer 4.1.7, p. 358.
    No compact support or whole operator
    separability is assumed in this local
    approximation theorem. *)
Theorem current_class_one_smoothing_uniform r (f:X->Y) (df:X->J 1%N) (g:R->E):
  0<r->norm_class hNX hNY (fun _=>True) f 1%N->
  (forall x,has_norm_higher_differential NX ej JN (fun _=>True) f 1%N x (df x))->
  (forall e,0<e->e<r->is_smoothing_convolution hNY (family e) f (ev (g e)))->
  forall K:smooth_compact_set hNX (fun _=>True),forall eta:R,0<eta->
    exists delta:R,0<delta /\delta<=r /\forall e,0<e->e<delta->
      forall x,smooth_compact_carrier K x->
        NY (ev (g e) x-f x)<eta /\ NZ (fv (d (g e)) x-L (df x))<eta.
Proof.
move=>hr hClass hActual hConvolution K eta hEta.
have [_ [a [hA hContinuous]]]:=hClass.
have hEqual:a=df.
  apply:funext=>x;exact:(norm_higher_differential_unique hNX hNY hJ
    (hA x Logic.I) (hActual x)).
rewrite hEqual in hContinuous.
have hBeta:=@norm_class_zero_postcompose R X (J 1%N) Z NX (@JN 1%N) NZ hN1
  (fun _=>True) df L hContinuous (@current_exterior_differential_map_bounded R h2 n m).
have hExteriorConvolution e (he:0<e) (her:e<r):
    is_smoothing_convolution hNZ (family e) (fun x=>L (df x)) (fv (d (g e))).
  exact:(@current_class_one_exterior_convolution R h2 n m e f df (g e)
    he hClass hActual (hConvolution e he her)).
have [a0 [ha0 [ha0r hUniform0]]]:=@continuous_smoothing_eventual_uniform R n Y NY hNY
  (@current_form_complete R h2 n m) kernel (@SmoothingKernel.laws R n)
  family (@SmoothingDilation.laws R n kernel) f (fun e=>ev (g e)) r hr
  (norm_class_continuous hClass) hConvolution K eta hEta.
have [a1 [ha1 [ha1r hUniform1]]]:=@continuous_smoothing_eventual_uniform R n Z NZ hNZ
  (@current_form_complete R h2 n m.+1) kernel (@SmoothingKernel.laws R n)
  family (@SmoothingDilation.laws R n kernel) (fun x=>L (df x)) (fun e=>fv (d (g e)))
  r hr hBeta hExteriorConvolution K eta hEta.
exists (Num.min a0 a1);split;first by rewrite lt_min ha0 ha1.
have hMin0:Num.min a0 a1<=a0 by rewrite ge_min lexx.
split;first exact:le_trans hMin0 ha0r.
move=>e he hSmall x hx.
have /andP [he0 he1]:(e<a0)&&(e<a1) by rewrite -lt_min.
split;[exact:hUniform0 e he he0 x hx|exact:hUniform1 e he he1 x hx].
Qed.
End CurrentClassOneSmoothingUniform.
