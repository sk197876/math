(** Federer (1969), 4.1.2, p. 347: smoothing
    is a linear operator on the original abstract
    smooth-function space. Its values are specified
    by the actual convolution integral before
    existence or an implementation is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import MeasureVectorIntegralUP Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smooth_smoothing_operator]: the original
    f |-> Phi_epsilon*f on E(R^n,Y),
    supporting the regularisation assertion in
    Federer 4.1.2, p. 347. *)
Definition is_smooth_smoothing_operator (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->R_n R n->Y)
    (psi:R_n R n->R) (P:Hom E E):=
  forall f:E,is_smoothing_convolution hNY psi (ev f) (ev (P f)).

(** Source for [is_smooth_smoothing_family]: every positive scale
    has its original integral operator, Federer 4.1.2,
    p. 347. No value at a
    nonpositive scale is prescribed. *)
Definition is_smooth_smoothing_family (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->R_n R n->Y)
    (family:R->R_n R n->R) (P:R->Hom E E):=
  forall e:R,0<e ->is_smooth_smoothing_operator hNY ev (family e) (P e).

(** Source for [smooth_smoothing_operator_unique]: the actual
    smoothing operator is uniquely determined by
    its original integral values, supporting
    Federer 4.1.2, p. 347. *)
Lemma smooth_smoothing_operator_unique (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R) (P Q:Hom E E):
  is_smooth_smoothing_operator hNY ev psi P ->
  is_smooth_smoothing_operator hNY ev psi Q ->P=Q.
Proof.
move=>hP hQ; apply:hom_ext=>f; apply:(smooth_function_extensional hE)=>x _.
exact:(measure_vector_integral_unique (hP f x) (hQ f x)).
Qed.
