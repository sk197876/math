(** Federer (1969), 4.1.14, p. 370: an independently specified
    smooth approximating family on one neighbourhood Z of K.
    This chosen-family interface strengthens the printed derivative
    bound on K to the same sharp bound on Z. It is used only for
    existence. The universal pushforward convergence statement must
    still accept every sequence with only the original bounds on K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormRegularity
  SmoothCompactSet LipschitzUP CurrentMapDifferential EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothApproximationUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).

(** Source for [is_current_compact_smooth_approximation]: the
    existence and uniform convergence paragraph of Federer 4.1.14,
    p. 370, and its subsequent appeal to 2.10.43, p. 201, for the
    sharp compact-restriction Lipschitz constant. The supplied maps
    are total representatives, with class and image laws on Z only. *)
Record is_current_compact_smooth_approximation
    (U:set X) (V:set Y) (K:smooth_compact_set hNX U)
    (f:X->Y) (L:R) (Z:set X) (g:nat->X->Y):Prop:={
  (** Source: Lip(f restricted to K) is nonnegative, 2.2.7, p. 64. *)
  current_compact_smooth_bound_nonnegative:0<=L;
  (** Source: Z is an open neighbourhood of K in U, 4.1.14, p. 370. *)
  current_compact_smooth_domain_open:
    forall x,Z x->norm_domain_interior NX Z x;
  (** Source: Z contains K, 4.1.14, p. 370. *)
  current_compact_smooth_domain_contains:smooth_compact_carrier K `<=` Z;
  (** Source: Clos Z is compact, 4.1.14, p. 370. *)
  current_compact_smooth_closure_compact:
    @compact (real_norm_metric_space hNX)
      (@closure (real_norm_metric_space hNX) Z);
  (** Source: Clos Z is contained in U, 4.1.14, p. 370. *)
  current_compact_smooth_closure_in_domain:
    @closure (real_norm_metric_space hNX) Z `<=` U;
  (** Source: the empty compact index is allowed, 4.1.14, p. 370;
      the chosen neighbourhood is empty, without an inhabitant of V. *)
  current_compact_smooth_empty_domain:
    smooth_compact_carrier K=set0->Z=set0;
  (** Source: every approximant has values in the original V,
      4.1.14, p. 370. No ambient V-valued extension is assumed. *)
  current_compact_smooth_image:forall i x,Z x->V (g i x);
  (** Source: each g_i has class infinity, 4.1.14, p. 370. *)
  current_compact_smooth_class:forall i,norm_class_all_orders hNX hNY Z (g i);
  (** Source: the smoothing maps have a common Lipschitz constant,
      4.1.14, p. 370. The sharp bound is supplied by 2.10.43. *)
  current_compact_smooth_lipschitz:forall i,
    @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
      (real_norm_metric_space hNY) Z (g i) L;
  (** Source: the original actual differential bound in 4.1.14,
      p. 370. It is proved from smoothness and the pairwise bound;
      the caller supplies no additional differential field. *)
  current_compact_smooth_differential_bound:forall i x,Z x->
    @euclidean_operator_norm R n nu
      (@current_map_differential R n nu Z (g i) x)<=L;
  (** Source: uniform convergence to f on K, 4.1.14, p. 370. *)
  current_compact_smooth_uniform:forall eta:R,0<eta->exists N:nat,
    forall i:nat,(N<=i)%N->forall x,smooth_compact_carrier K x->
      NY (g i x-f x)<eta
}.
End CurrentCompactSmoothApproximationUP.
