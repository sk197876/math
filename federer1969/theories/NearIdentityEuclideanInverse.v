(** Supporting linear perturbation estimate for Federer (1969), 2.10.5(2),
    p. 173, compact convex projection continuity. A Euclidean endomorphism
    differing from the identity by at most one half on the unit ball is
    invertible, and its inverse increases norms by at most two. This is the
    identity case of the perturbation estimates in 2.7.16, p. 134, using the
    operator-norm laws of 1.7.6, pp. 33–34. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities EuclideanLinearMaps LinearGroupEstimates
  OperatorNormUP OperatorNormLaws OperatorNorm TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [near_identity_euclidean_inverse_bound]:
    supporting uniformly bounded inverse for
    nearby projected sections in Federer
    2.10.5(2), p. 173. The inverse is proved
    to exist from the unit-ball estimate; no
    continuity or invertibility is assumed. *)
Theorem near_identity_euclidean_inverse_bound (R : realType) n
    (f : {linear R_n R n -> R_n R n}) :
  (forall x, inner_norm (@euclidean_inner_productP R n) x<=1 ->
    inner_norm (@euclidean_inner_productP R n) (f x-x)<=(2:R)^-1) ->
  exists g : {linear R_n R n -> R_n R n}, cancel f g /\ cancel g f /\
    forall y, inner_norm (@euclidean_inner_productP R n) (g y)<=
      2*inner_norm (@euclidean_inner_productP R n) y.
Proof.
move=> hunit.
pose V := R_n R n.
pose hB := @euclidean_inner_productP R n.
pose N := inner_norm hB.
pose D := linear_difference_map f (linear_id V).
pose L := linear_operator_norm hB hB (@coordinate_basisP R n) D.
have hL : L<=(2:R)^-1.
  apply/(operator_norm_le_unit (linear_operator_normP hB hB (@coordinate_basisP R n) D)).
  exact hunit.
have hnear x : N (f x-x)<=(2:R)^-1*N x.
  apply: le_trans (@linear_operator_norm_bound R V V _ _ hB hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) D x) _.
  change (is_true (L*N x<=(2:R)^-1*N x)).
  apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  exact hL.
have hinj : injective f.
  move=> x y hxy.
  have h0 : f (x-y)=0 by rewrite linearB hxy subrr.
  have hz : N (x-y)<=(2:R)^-1*N (x-y).
    by move: (hnear (x-y)); rewrite h0 /N sub0r inner_normN.
  have hn : 0<=N (x-y) := inner_norm_nonnegative hB _.
  have hz0 : N (x-y)=0 by lra.
  apply/eqP; rewrite -subr_eq0 -(inner_norm_eq0 hB).
  change (is_true (N (x-y)==0)); by rewrite hz0 eqxx.
have [g [hfg hgf]] := euclidean_linear_inverse hinj.
exists g; split=> //; split=> // y.
have herr := hnear (g y); rewrite hgf in herr.
have htri := @inner_norm_triangle R V _ hB (g y-y) y.
rewrite subrK in htri.
change (is_true (N (g y)<=N (g y-y)+N y)) in htri.
have he : N (g y-y)=N (y-g y) by rewrite /N -[g y-y]opprB inner_normN.
rewrite he in htri.
change (is_true (N (g y)<=2*N y)); lra.
Qed.
