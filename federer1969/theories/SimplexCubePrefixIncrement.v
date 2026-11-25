(** Federer (1969), 4.1.27, p. 384:
    each prefix product is affine in
    any one coordinate. Its exact coordinate
    increment is the increment times the
    product with that factor omitted. This
    identity permits zero coordinates throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct SimplexCubeParametrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_omitted_prefix]: the coefficient
    obtained by omitting the j-th factor
    of the original prefix product, supporting
    the displayed differential in 4.1.27, p. 384. *)
Definition simplex_cube_omitted_prefix (R:realType) m
    (x:R_n R m) k (j:'I_m):R:=
  \prod_(i:'I_m | (i<k)%N && (i!=j)) x i.

(** Source for [simplex_cube_prefix_coordinate_increment]: the exact
    coordinate increment of each prefix in
    the map of 4.1.27, p. 384.
    Both the present-factor and absent-factor cases
    retain every source point. *)
Theorem simplex_cube_prefix_coordinate_increment (R:realType) m
    (x:R_n R m) k (j:'I_m) (h:R):
  simplex_cube_prefix_product (x+h*:@coordinate_basis R m j) k-
    simplex_cube_prefix_product x k=
      h*(if (j<k)%N then simplex_cube_omitted_prefix x k j else 0).
Proof.
have hCoordinate i:i!=j->(x+h*:@coordinate_basis R m j) i=x i.
  move=>hDifferent;rewrite /coordinate_basis !ffunE.
  change (x i+h*(if i==j then 1 else 0)=x i).
  by rewrite (negbTE hDifferent) mulr0 addr0.
case hJ:(j<k)%N.
- have hAt:(x+h*:@coordinate_basis R m j) j=x j+h.
    rewrite /coordinate_basis !ffunE.
    change (x j+h*(if j==j then 1 else 0)=x j+h).
    by rewrite eqxx mulr1.
  have hOther:(\prod_(i:'I_m | (i<k)%N && (i!=j))
      (x+h*:@coordinate_basis R m j) i)=simplex_cube_omitted_prefix x k j.
    apply:eq_bigr=>i /andP[_ hDifferent];exact:hCoordinate i hDifferent.
  rewrite /simplex_cube_prefix_product (bigD1 j) //= hAt hOther.
  rewrite (bigD1 j) //=.
  by rewrite -/(simplex_cube_omitted_prefix x k j) mulrDl addrAC subrr add0r.
- have hSame:simplex_cube_prefix_product (x+h*:@coordinate_basis R m j) k=
      simplex_cube_prefix_product x k.
    apply:eq_bigr=>i hI;apply:hCoordinate.
    apply/eqP=>hEqual;move:hI;by rewrite hEqual hJ.
  by rewrite hSame subrr mulr0.
Qed.
