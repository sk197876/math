(** Federer (1969), 4.1.2, p. 347: the
    original convolution retains the measurable field's
    partial domain. Its weights are source-dependent
    scalar multiples; no value is assigned at
    a point where that field is undefined. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionSourcePostcomposition
  MeasureVectorIntegralUP GrassmannAbbreviations EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_scalar_vector_weight]: the actual integrand
    Phi(x-z) f(z), Federer 4.1.2, p. 347,
    under the partial-function convention of 2.3.1, p. 72. *)
Definition partial_scalar_vector_weight (R:realType) (X:Type) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (w:X->R)
    (f:partial_function X (real_norm_metric_space hNY)):
    partial_function X (real_norm_metric_space hNY):=
  partial_function_source_postcompose f (fun x y=>(w x*:y:real_norm_metric_space hNY)).

(** Source for [is_partial_smoothing_convolution]: the first original
    convolution formula of Federer 4.1.2, p. 347,
    retaining its exact integrand domain. Existence is
    a separate theorem. *)
Definition is_partial_smoothing_convolution (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (psi:R_n R n->R)
    (f:partial_function (R_n R n) (real_norm_metric_space hNY)) (g:R_n R n->Y):=
  forall x,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_scalar_vector_weight (fun z=>psi (x-z)) f) (g x).

(** Source for [partial_smoothing_convolution_unique]: uniqueness of the
    original partial-field convolution, implicit in Federer 4.1.2,
    p. 347, follows from vector-integral uniqueness. *)
Lemma partial_smoothing_convolution_unique (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (psi:R_n R n->R)
    (f:partial_function (R_n R n) (real_norm_metric_space hNY)) (g h:R_n R n->Y):
  is_partial_smoothing_convolution psi f g ->is_partial_smoothing_convolution psi f h ->g=h.
Proof. move=>hg hh; apply:funext=>x; exact:(measure_vector_integral_unique (hg x) (hh x)). Qed.
