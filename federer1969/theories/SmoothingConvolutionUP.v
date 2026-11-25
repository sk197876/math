(** Federer (1969), 4.1.2, p. 347: exact
    vector integral specification of the original convolution.
    Existence, smoothness and approximation are proved after
    this definition and are not assumptions of its laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureVectorIntegralUP
  GrassmannAbbreviations EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smoothing_convolution]: the exact original
    formula (Phi*f)(x)=integral Phi(x-z) f(z) dz,
    Federer 4.1.2, p. 347, specified by
    the proved Banach-valued integral laws of 2.4.12. *)
Definition is_smoothing_convolution (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (phi:R_n R n->R)
    (f g:R_n R n->Y):=
  forall x,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(phi (x-z)*:f z:real_norm_metric_space hNY))) (g x).

(** Source for [smoothing_convolution_unique]: the actual
    original convolution is uniquely determined by its
    integral evaluations, supporting Federer 4.1.2, p. 347. *)
Lemma smoothing_convolution_unique (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (phi:R_n R n->R) (f g h:R_n R n->Y):
  is_smoothing_convolution hNY phi f g ->is_smoothing_convolution hNY phi f h ->g=h.
Proof. move=>hg hh; apply:funext=>x; exact:(measure_vector_integral_unique (hg x) (hh x)). Qed.
