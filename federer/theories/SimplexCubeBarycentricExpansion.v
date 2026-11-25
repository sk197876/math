(** Federer (1969), 4.1.27, p. 384:
    the original opaque prefix-product map equals
    its barycentric expression. On the open
    unit cube the coefficients are positive
    and sum to one, including for
    repeated vertices and the empty source dimension. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanOpenUnitCube
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeBarycentricCoefficients FiniteConsecutiveEdgeTelescope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_barycentric_expansion]: the algebraic
    conversion between the two displayed expressions
    in 4.1.27, p. 384. It holds
    at every source point, without cube
    membership or affine independence. *)
Theorem simplex_cube_barycentric_expansion (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  @SimplexCubeParametrisation.value R n m v x=
    \sum_(i:'I_(m.+1)) simplex_cube_barycentric_coefficient x i*:v i.
Proof.
pose p:=simplex_cube_prefix_product x.
pose w:=fun k:nat=>v (inord k).
have hVertex:forall i:'I_(m.+1),w (val i)=v i.
  by move=>i;rewrite /w inord_val.
have hLeft:p 0%N*:w 0%N+\sum_(i<m) p i.+1*:(w i.+1-w i)=
    @SimplexCubeParametrisation.value R n m v x.
  rewrite /p (@simplex_cube_prefix_zero R m x) scale1r (@hVertex ord0)
    (@SimplexCubeParametrisation.laws R n m v x).
  congr (v ord0+_);apply:eq_bigr=>i _.
  have hNext:w i.+1=v (lift ord0 i) by rewrite -hVertex.
  by rewrite hNext (@hVertex (widen_ord (leqnSn m) i)).
have hRight: \sum_(i<m) (p i-p i.+1)*:w i+p m*:w m=
    \sum_(i:'I_(m.+1)) simplex_cube_barycentric_coefficient x i*:v i.
  rewrite big_ord_recr /simplex_cube_barycentric_coefficient /= ltnn
    (@hVertex ord_max).
  congr (_+p m*:v ord_max);apply:eq_bigr=>i _.
  by rewrite ltn_ord (@hVertex (widen_ord (leqnSn m) i)).
exact:(eq_trans (esym hLeft)
  (eq_trans (@finite_consecutive_edge_telescope R (R_n R n) p w m) hRight)).
Qed.

(** Source for [simplex_cube_image_positive_barycentric]: every
    original cube image has strictly positive
    barycentric coefficients, one inclusion of the
    exact image assertion of 4.1.27, p. 384.
    The converse is a separate law. *)
Theorem simplex_cube_image_positive_barycentric (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (@SimplexCubeParametrisation.value R n m v) @` (@euclidean_open_unit_cube R m) `<=`
    simplex_positive_barycentric_image v.
Proof.
move=>y [x hx <-];exists (simplex_cube_barycentric_coefficient x).
split;first exact:(@simplex_cube_barycentric_positive R m x hx).
split;[exact:simplex_cube_barycentric_sum|exact:simplex_cube_barycentric_expansion].
Qed.
