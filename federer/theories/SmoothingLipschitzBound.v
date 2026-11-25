(** Federer (1969), 4.1.2, p. 347, used in
    the smooth tests of 4.1.12, p. 369:
    convolution by the original nonnegative unit-mass
    kernel preserves a Lipschitz bound. Reuse the
    two original convolution integrals and their proved
    weighted difference estimate. No kernel symmetry is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingDilationIntegral SmoothingConvolutionUP NormedSmoothingSubstitution UnitKernelVectorDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_lipschitz_bound]: the actual
    positive normalized regularisation preserves the original
    Lipschitz constant, by Federer 4.1.2, p. 347.
    This supplies the exact derivative bound needed for
    the printed test functions in 4.1.12, p. 369.
    The target is any normed space for which the
    displayed original convolution exists. *)
Theorem smoothing_lipschitz_bound (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (phi:R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (family:R->R_n R n->R)
    (hFamily:is_smoothing_dilation phi family) e (f g:R_n R n->Y) L:
  0<e->is_smoothing_convolution hNY (family e) f g->
  (forall x y,NY (f x-f y)<=L*inner_norm (@euclidean_inner_productP R n) (x-y))->
  forall x y,NY (g x-g y)<=L*inner_norm (@euclidean_inner_productP R n) (x-y).
Proof.
move=>he hConvolution hL x y.
apply:(@unit_weight_vector_difference_bound R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (family e) (fun z=>f (x-z)) (fun z=>f (y-z)) (g x) (g y)
  (L*inner_norm (@euclidean_inner_productP R n) (x-y))
  (@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he)
  (@smoothing_dilation_integral_one R n phi family hPhi hFamily e he)
  (@normed_smoothing_convolution_alternate_integral R n Y NY hNY (family e) f g hConvolution x)
  (@normed_smoothing_convolution_alternate_integral R n Y NY hNY (family e) f g hConvolution y))=>z _.
have h:=hL (x-z) (y-z).
have hDifference:(x-z)-(y-z)=x-y by rewrite opprB addrA subrK.
by rewrite hDifference in h.
Qed.
