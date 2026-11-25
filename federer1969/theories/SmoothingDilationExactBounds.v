(** Federer (1969), 4.1.2, pp. 346–347:
    the original derivative-supremum equality for every
    positive kernel scale and every derivative degree.
    All derivative fields are actual higher differentials;
    the global bounds come from compact support. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm NormHigherDifferentialUP
  UniformFunctionNormUP SmoothingKernelUP SmoothingDilationUP SmoothingKernelDerivativeBounds
  SmoothingDilationDerivatives ScaledArgumentUniformNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothingDilationExactBounds.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation ev := (fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [smoothing_dilation_exact_derivative_norm]: the
    finite original supremum for the kth kernel derivative
    scales by epsilon^(-n-k), the exact equality
    in Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_exact_derivative_norm e k:0<e ->
  exists (D0 D:X->Z k) (G:R),
    (forall x,has_norm_higher_differential N ev ZN (fun _=>True) phi k x (D0 x)) /\
    is_uniform_function_norm (fun x=>ZN k (D0 x)) G /\
    (forall x,has_norm_higher_differential N ev ZN (fun _=>True) (family e) k x (D x)) /\
    is_uniform_function_norm (fun x=>ZN k (D x)) (G/(e^+(n+k))).
Proof.
move=>he.
have [D0 [G [hD0 hG]]]:=@smoothing_kernel_derivative_supremum_exists R n phi hPhi k.
pose D:=fun x=>(e^+(n+k))^-1*:D0 (e^-1*:x).
exists D0,D,G; split; first exact hD0.
split; first exact hG.
split.
- exact:(@smoothing_dilation_higher_differential R n phi family hFamily Z ev ZN hZ k D0 hD0 e he).
- exact:(@scaled_argument_exact_uniform_norm R X (Z k) (ZN k)
    (continuous_multilinear_norm_is_norm hR (hZ k)) D0 n k G e he hG).
Qed.
End SmoothingDilationExactBounds.
