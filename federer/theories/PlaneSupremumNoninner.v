(** Federer (1969), 2.10.44, printed p. 202: the displayed supremum norm is
    not induced by an inner product. Verify this using the parallelogram law
    of 1.7.13, p. 37, at the two coordinate unit vectors. The abstract
    supremum-norm evaluation law suffices; no private maximum construction
    is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GrassmannAbbreviations InnerProductUP InnerNorm InnerParallelogram
  EuclideanRealPlane PlaneSupremumNorm PlanePairNormGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [plane_supremum_norm_not_inner]: direct
    non-inner-product qualification of the norm mu
    in 2.10.44, p. 202. Its values on
    e_1, e_2, e_1+e_2 and e_1-e_2 are
    all one, contradicting the parallelogram law. *)
Theorem plane_supremum_norm_not_inner (R : realType) :
  ~ exists B : R_n R 2 -> R_n R 2 -> R,
    exists hB : is_inner_product B,
      forall x, inner_norm hB x=plane_supremum_norm x.
Proof.
move=> [B [hB heq]].
pose u := @euclidean_real_plane_pair R 1 0.
pose v := @euclidean_real_plane_pair R 0 1.
have hu : plane_supremum_norm u= 1.
  by rewrite plane_supremum_normE /u real_plane_pair_first_coordinate
    real_plane_pair_second_coordinate normr1 normr0 max_l // ler01.
have hv : plane_supremum_norm v= 1.
  by rewrite plane_supremum_normE /v real_plane_pair_first_coordinate
    real_plane_pair_second_coordinate normr1 normr0 max_r // ler01.
have hp : plane_supremum_norm (u+v)= 1.
  rewrite plane_supremum_normE [((u+v) ord0)]ffunE [((u+v) ord_max)]ffunE
    /u /v !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate.
  by rewrite addr0 add0r normr1 maxxx.
have hm : plane_supremum_norm (u-v)= 1.
  rewrite plane_supremum_normE [((u-v) ord0)]ffunE [((u-v) ord_max)]ffunE
    [((-v) ord0)]ffunE [((-v) ord_max)]ffunE
    /u /v !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate.
  by rewrite subr0 sub0r normrN normr1 maxxx.
have hh := inner_parallelogram hB u v.
rewrite !heq hu hv hp hm in hh; lra.
Qed.
