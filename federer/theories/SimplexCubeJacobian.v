(** Federer (1969), 4.1.27, p. 384:
    D_1 f wedge ... wedge D_m f
    equals x_1^(m-1) ... x_(m-1) times
    the consecutive-edge vector zeta. The proof
    uses the actual differential columns and
    the earlier finite exterior expansion; dependent
    vertices and zero source coordinates remain allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers CurrentMapDifferential
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubePrefixIncrement SimplexCubeDifferentialColumns
  SimplexCubeDiagonalWeight UpperTriangularExteriorCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_omitted_diagonal_prefix]: the diagonal
    entry in the triangular differential of
    4.1.27, p. 384, is the product
    of all preceding coordinates. The coefficient
    formula is valid even when factors vanish. *)
Lemma simplex_cube_omitted_diagonal_prefix (R:realType) m
    (x:R_n R m) (i:'I_m):
  simplex_cube_omitted_prefix x (val i).+1 i=
    simplex_cube_prefix_product x (val i).
Proof.
rewrite /simplex_cube_omitted_prefix /simplex_cube_prefix_product.
apply:eq_bigl=>j;rewrite -val_eqE /= ltnS.
by rewrite ltn_neqAle andbC.
Qed.

(** Source for [simplex_cube_column_exterior_product]: the original
    upper triangular differential columns give the
    precise power product in 4.1.27,
    p. 384. No nondegeneracy premise or
    inverse coordinate factor is needed. *)
Theorem simplex_cube_column_exterior_product (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  e_lambda (simplex_cube_differential_column v x) (ord_tuple m)=
    simplex_cube_jacobian_weight x*:simplex_consecutive_orientation v.
Proof.
pose e:=simplex_consecutive_edge_family v.
pose a (i j:'I_m):R:=if (i<=j)%N then
  simplex_cube_omitted_prefix x (val j).+1 i else 0.
have hColumn:simplex_cube_differential_column v x=
    (fun i=>\sum_(j:'I_m) a i j*:e j).
  apply:funext=>i;rewrite /simplex_cube_differential_column /a big_mkcond.
  apply:eq_bigr=>j _;case:((i<=j)%N);by rewrite ?scale0r.
have hUpper:forall i j:'I_m,(j<i)%N->a i j=0.
  move=>i j hJI;rewrite /a.
  have hNo:~~(i<=j)%N by rewrite -ltnNge.
  by rewrite (negbTE hNo).
rewrite hColumn (@upper_triangular_exterior_coefficients R (R_n R n) m e a hUpper).
have hDiagonal:(\prod_(i:'I_m) a i i)=simplex_cube_jacobian_weight x.
  have hSame:(\prod_(i:'I_m) a i i)=
      \prod_(i:'I_m) simplex_cube_prefix_product x (val i).
    apply:eq_bigr=>i _;by rewrite /a leqnn simplex_cube_omitted_diagonal_prefix.
  rewrite hSame;exact:simplex_cube_diagonal_weight.
by rewrite hDiagonal.
Qed.

(** Source for [simplex_cube_wedge_differential]: the complete
    displayed wedge-Jacobian formula in 4.1.27,
    p. 384, for the actual differential
    of the independently specified opaque map.
    The equality holds at every x in
    R^m and includes m=0 and degenerate vertices. *)
Theorem simplex_cube_wedge_differential (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  e_lambda (fun j=>@current_map_differential R m n (fun _=>True)
    (@SimplexCubeParametrisation.value R n m v) x (@coordinate_basis R m j))
    (ord_tuple m)=simplex_cube_jacobian_weight x*:simplex_consecutive_orientation v.
Proof.
have hColumns:(fun j=>@current_map_differential R m n (fun _=>True)
    (@SimplexCubeParametrisation.value R n m v) x (@coordinate_basis R m j))=
      simplex_cube_differential_column v x.
  apply:funext=>j;exact:simplex_cube_map_differential_column.
rewrite hColumns;exact:simplex_cube_column_exterior_product.
Qed.
