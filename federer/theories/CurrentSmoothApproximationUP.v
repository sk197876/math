(** Federer (1969), 4.1.14, p. 370: every smooth sequence in
    the defining condition. Its derivative bound is required only
    on the printed compact K. Neither compact closure of the
    source neighbourhood nor a bound on its remainder is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct SmoothCompactSet CurrentMapDifferential EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothApproximationUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z:set X) (V:set Y).
Variable K:smooth_compact_set hNX Z.
Variable f:X->Y.
Variable g:nat->X->Y.

(** Source for [is_current_smooth_approximation]: exactly the
    class-infinity, finite derivative supremum on K and uniform
    approximation requirements in Federer 4.1.14, p. 370.
    A finite nonnegative real cap expresses boundedness and also
    covers empty K without choosing a special empty supremum. *)
Record is_current_smooth_approximation:Prop:={
  (** Source for [current_smooth_approximation_image]: g_i:Z->V,
      Federer 4.1.14, p. 370. *)
  current_smooth_approximation_image:forall i x,Z x->V (g i x);
  (** Source for [current_smooth_approximation_class]: each g_i
      has class infinity on Z, Federer 4.1.14, p. 370. *)
  current_smooth_approximation_class:forall i,
    norm_class_all_orders hNX hNY Z (g i);
  (** Source for [current_smooth_approximation_bound]: one finite
      bound for every i and x in K, Federer 4.1.14, p. 370.
      No differential bound on all Z is required. *)
  current_smooth_approximation_bound:exists c:R,0<=c /\
    forall i x,smooth_compact_carrier K x->
      @euclidean_operator_norm R n nu
        (@current_map_differential R n nu Z (g i) x)<=c;
  (** Source for [current_smooth_approximation_uniform]: uniform
      convergence to the original f on K, Federer 4.1.14, p. 370. *)
  current_smooth_approximation_uniform:forall epsilon:R,0<epsilon->
    exists N:nat,forall i:nat,(N<=i)%N->
      forall x,smooth_compact_carrier K x->NY (g i x-f x)<epsilon
}.
End CurrentSmoothApproximationUP.
