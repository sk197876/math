(** Federer (1969), 2.10.46, printed p. 203: apply the last paragraph of
    1.7.4, p. 31, to a projection and the second-coordinate projection of
    R^(m+n). The maps below are the prescribed coordinate maps of 2.6.5, p.
    120, not selected existence witnesses. Their linear and adjoint laws
    identify the second-coordinate map as an orthogonal projection. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinear CoordinateProjection InnerProductUP Bilinear AdjointUP OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_right_block]: direct second-coordinate
    projection (x,y) maps to y in the application of
    1.7.4 in 2.10.46, p. 203, expressed through
    the existing block-coordinate interface. *)
Definition euclidean_right_block (R : realType) m n (x : R_n R (m+n)) : R_n R n :=
  (@euclidean_block_split R m n x).2.

(** Source for [euclidean_right_block_linear]: supporting
    linearity of the second-coordinate projection used
    in 2.10.46, p. 203. Empty blocks are included. *)
Lemma euclidean_right_block_linear (R : realType) m n :
  linear (@euclidean_right_block R m n).
Proof.
by move=> a x y; apply/ffunP=> i; rewrite /euclidean_right_block /euclidean_block_split !ffunE.
Qed.
HB.instance Definition _ (R : realType) m n := GRing.isLinear.Build R (R_n R (m+n)) (R_n R n)
  *:%R (@euclidean_right_block R m n) (@euclidean_right_block_linear R m n).

(** Source for [euclidean_right_block_injection]: supporting
    adjoint coordinate inclusion y maps to (0,y) for
    the projection in 2.10.46, p. 203; coordinate
    adjoints are described in 1.7.4, p. 31. *)
Definition euclidean_right_block_injection (R : realType) m n (y : R_n R n) : R_n R (m+n) :=
  @euclidean_block_join R m n (0,y).

(** Source for [euclidean_right_block_injection_linear]: supporting
    linearity of that coordinate adjoint in the
    1.7.4 application of 2.10.46, p. 203. *)
Lemma euclidean_right_block_injection_linear (R : realType) m n :
  linear (@euclidean_right_block_injection R m n).
Proof.
move=> a x y; have hh := @euclidean_block_join_linear R m n a (0,x) (0,y).
change (@euclidean_block_join R m n (a*:0+0,a*:x+y)=
  a*:(@euclidean_block_join R m n (0,x))+(@euclidean_block_join R m n (0,y))) in hh.
by rewrite scaler0 add0r in hh.
Qed.
HB.instance Definition _ (R : realType) m n := GRing.isLinear.Build R (R_n R n) (R_n R (m+n))
  *:%R (@euclidean_right_block_injection R m n) (@euclidean_right_block_injection_linear R m n).

(** Source for [euclidean_right_block_pair]: direct evaluation
    of the second-coordinate map on a paired point,
    used in the displayed factor identity of 2.10.46, p. 203. *)
Lemma euclidean_right_block_pair (R : realType) m n (x : R_n R m) (y : R_n R n) :
  euclidean_right_block (@euclidean_block_join R m n (x,y))=y.
Proof. by rewrite /euclidean_right_block euclidean_block_joinK. Qed.

(** Source for [euclidean_right_block_orthogonal_projection]: supporting
    membership in O*(m+n,n) for the second-coordinate
    projection used with 1.7.4 in 2.10.46, p. 203.
    Its actual adjoint is the zero-first-block inclusion. *)
Theorem euclidean_right_block_orthogonal_projection (R : realType) m n :
  O_star (GRing.Linear.clone _ _ _ _ (@euclidean_right_block R m n) _).
Proof.
exists (GRing.Linear.clone _ _ _ _ (@euclidean_right_block_injection R m n) _); split.
- move=> x y; rewrite /euclidean_right_block_injection euclidean_block_join_inner /=.
  by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R m))) add0r.
- move=> x y.
  rewrite /euclidean_right_block_injection -[y](@euclidean_block_splitK R m n) euclidean_block_join_inner /=.
  rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R m))) add0r.
  by rewrite /euclidean_right_block euclidean_block_joinK.
Qed.
