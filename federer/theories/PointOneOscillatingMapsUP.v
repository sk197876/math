(** Federer (1969), 4.1.15, p. 373: independent
    quantitative specification of a compact smooth sequence
    realising the printed failure of image convergence.
    Existence is proved separately; no current conclusion
    is built into these laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormRegularity GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointOneOscillatingMapsUP.
Variable R:realType.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation Id:=(hom_of_linear (@linear_id R X)).

(** Source for [is_point_one_oscillating_maps]: the compact
    smooth maps in the last paragraph of 4.1.15,
    p. 373, may be chosen with zero value at
    zero, slopes (-1)^i, size at most 2/(i+1)
    and one global Lipschitz bound. The following
    existence proof derives these additional quantitative witnesses. *)
Record is_point_one_oscillating_maps (u:nat->X->X):Prop:={
  (** Source for [point_one_oscillating_smooth]: smoothness in
      the last example of 4.1.15, p. 373. *)
  point_one_oscillating_smooth:forall i,
    norm_class_all_orders hNX hNX Full (u i);
  (** Source for [point_one_oscillating_zero]: the chosen
      example fixes zero, supporting 4.1.15, p. 373. *)
  point_one_oscillating_zero:forall i,u i 0=0;
  (** Source for [point_one_oscillating_size]: a quantitative
      uniform-zero bound for the sequence in 4.1.15, p. 373. *)
  point_one_oscillating_size:forall i x,NX (u i x)<=2/i.+1%:R;
  (** Source for [point_one_oscillating_origin_differential]: the
      actual slopes alternate, as required by 4.1.15, p. 373. *)
  point_one_oscillating_origin_differential:forall i,
    has_norm_differential NX NX Full (u i) (0:X) ((-1:R)^+i*:Id);
  (** Source for [point_one_oscillating_lipschitz]: one finite
      bound independent of i supplies the printed uniform
      differential bounds of 4.1.15, p. 373. *)
  point_one_oscillating_lipschitz:exists L:R,0<L /\forall i x y,
    NX (u i x-u i y)<=L*NX (x-y);
  (** Source for [point_one_oscillating_off]: the chosen
      maps have a common compact support, as required for
      the scalar test functions in 4.1.15, p. 373. *)
  point_one_oscillating_off:forall i x,2<=NX x->u i x=0
}.
End PointOneOscillatingMapsUP.
