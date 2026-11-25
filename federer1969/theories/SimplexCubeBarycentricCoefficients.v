(** Federer (1969), 4.1.27, p. 384:
    consecutive prefix differences give the positive
    barycentric coefficients of the original cube
    parametrisation. The last coefficient is the
    full product. Existing finite products and
    the earlier telescoping sum supply the laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanOpenUnitCube
  SimplexCubeParametrisationUP CosetLoneIntegralOnto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_prefix_zero]: the empty
    initial product in the original f,
    4.1.27, p. 384, is one. *)
Lemma simplex_cube_prefix_zero (R:realType) m (x:R_n R m):
  simplex_cube_prefix_product x 0%N= 1.
Proof.
rewrite /simplex_cube_prefix_product.
apply:big_pred0=>i;exact:ltn0.
Qed.

(** Source for [simplex_cube_prefix_successor]: adjoining
    x_(k+1) gives the next original prefix
    product, supporting 4.1.27, p. 384. *)
Lemma simplex_cube_prefix_successor (R:realType) m (x:R_n R m) k
    (hK:(k<m)%N):
  simplex_cube_prefix_product x k.+1=
    x (Ordinal hK)*simplex_cube_prefix_product x k.
Proof.
rewrite /simplex_cube_prefix_product (bigD1 (Ordinal hK)) /=;last exact:ltnSn.
congr (x (Ordinal hK)*_).
apply:eq_bigl=>i.
by rewrite -val_eqE /= ltnS ltn_neqAle andbC.
Qed.

(** Source for [simplex_cube_prefix_positive]: every original
    prefix product is positive on the open
    unit cube, supporting the image assertion
    in 4.1.27, p. 384. This includes
    the empty coordinate family. *)
Lemma simplex_cube_prefix_positive (R:realType) m (x:R_n R m) k:
  euclidean_open_unit_cube x->0<simplex_cube_prefix_product x k.
Proof.
move=>hCube;rewrite /simplex_cube_prefix_product.
apply:prodr_gt0=>i _;exact:(andP (hCube i)).1.
Qed.

(** Source for [simplex_cube_prefix_strict_step]: each new
    coordinate in (0,1) strictly decreases a
    positive prefix product, supporting 4.1.27,
    p. 384. No division is used. *)
Lemma simplex_cube_prefix_strict_step (R:realType) m (x:R_n R m) k
    (hK:(k<m)%N):
  euclidean_open_unit_cube x->
  simplex_cube_prefix_product x k.+1<simplex_cube_prefix_product x k.
Proof.
move=>hCube;rewrite (@simplex_cube_prefix_successor R m x k hK).
rewrite -[X in _<X]mul1r
  (ltr_pM2r (@simplex_cube_prefix_positive R m x k hCube)).
exact:(andP (hCube (Ordinal hK))).2.
Qed.

(** Source for [simplex_cube_barycentric_coefficient]: the original
    positive coefficients in the displayed image
    of 4.1.27, p. 384, written as
    successive prefix differences and their final
    remainder. This is an auxiliary finite formula,
    not a second choice of the cube map. *)
Definition simplex_cube_barycentric_coefficient (R:realType) m
    (x:R_n R m) (i:'I_(m.+1)):R:=
  if (i<m)%N then simplex_cube_prefix_product x (val i)-
    simplex_cube_prefix_product x (val i).+1
  else simplex_cube_prefix_product x m.

(** Source for [simplex_cube_barycentric_positive]: all coefficients
    are strictly positive on the original open
    unit cube, including the single coefficient
    at m=0, supporting 4.1.27, p. 384. *)
Lemma simplex_cube_barycentric_positive (R:realType) m (x:R_n R m):
  euclidean_open_unit_cube x->forall i,0<simplex_cube_barycentric_coefficient x i.
Proof.
move=>hCube i;rewrite /simplex_cube_barycentric_coefficient.
case hI:(i<m)%N.
- rewrite subr_gt0;exact:(@simplex_cube_prefix_strict_step R m x (val i) hI hCube).
- exact:(@simplex_cube_prefix_positive R m x m hCube).
Qed.

(** Source for [simplex_cube_barycentric_sum]: the positive
    barycentric coefficients sum to one, the
    normalization in the original image display
    of 4.1.27, p. 384. The existing
    finite telescoping theorem includes m=0. *)
Lemma simplex_cube_barycentric_sum (R:realType) m (x:R_n R m):
  (\sum_(i:'I_(m.+1)) simplex_cube_barycentric_coefficient x i)= 1.
Proof.
rewrite big_ord_recr /simplex_cube_barycentric_coefficient /= ltnn.
have hHead:(\sum_(i:'I_m)
    (if (i<m)%N then simplex_cube_prefix_product x (val i)-
      simplex_cube_prefix_product x (val i).+1 else simplex_cube_prefix_product x m))=
    \sum_(i:'I_m) (simplex_cube_prefix_product x (val i)-
      simplex_cube_prefix_product x (val i).+1).
  apply:eq_bigr=>i _;by rewrite ltn_ord.
by rewrite hHead (@telescoping_real_sum R (simplex_cube_prefix_product x) m)
  subrK simplex_cube_prefix_zero.
Qed.
