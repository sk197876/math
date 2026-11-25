(** Federer (1969), 4.1.27, p. 384:
    the original prefix-product map is injective
    on the open cube when the vertices
    are affinely independent. First recover normalized
    barycentric coefficients, then their successive positive
    prefix products and the actual cube coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOpenUnitCube CurrentSimplexFrame SimplexCubeParametrisationUP
  SimplexCubeParametrisationSealed SimplexCubeBarycentricCoefficients
  SimplexCubeBarycentricExpansion SimplexBarycentricUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_barycentric_prefix_unique]: equality
    of all original barycentric coefficients identifies
    all prefix products, supporting the injectivity
    statement of 4.1.27, p. 384.
    This implication itself requires no positivity. *)
Lemma simplex_cube_barycentric_prefix_unique (R:realType) m
    (x y:R_n R m):
  (forall i,simplex_cube_barycentric_coefficient x i=
    simplex_cube_barycentric_coefficient y i)->
  forall k,(k<=m)%N->simplex_cube_prefix_product x k=simplex_cube_prefix_product y k.
Proof.
move=>hCoefficients k;elim:k=>[|k ih] hK.
- by rewrite !simplex_cube_prefix_zero.
- have hPrevious:(k<=m)%N:=leq_trans (leqnSn k) hK.
  have hIndex:(k<m.+1)%N:=leq_ltn_trans hPrevious (ltnSn m).
  have hCoefficient:=hCoefficients (Ordinal hIndex).
  rewrite /simplex_cube_barycentric_coefficient /= hK (ih hPrevious) in hCoefficient.
  have hRecovery:=congr1 (fun a:R=>simplex_cube_prefix_product y k-a) hCoefficient.
  by rewrite !subKr in hRecovery.
Qed.

(** Source for [simplex_cube_parametrisation_injective]: the original
    injectivity assertion in 4.1.27, p. 384.
    The source nondegeneracy condition is expressed
    by the already defined independence of
    u_1-u_0,...,u_m-u_0. Empty source dimension remains included. *)
Theorem simplex_cube_parametrisation_injective (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex v->
  forall x y:R_n R m,euclidean_open_unit_cube x->euclidean_open_unit_cube y->
    @SimplexCubeParametrisation.value R n m v x=
      @SimplexCubeParametrisation.value R n m v y->x=y.
Proof.
move=>hIndependent x y hX hY hImage.
rewrite !simplex_cube_barycentric_expansion in hImage.
have hCoefficients:=@simplex_nondegenerate_barycentric_unique R n m v
  (simplex_cube_barycentric_coefficient x) (simplex_cube_barycentric_coefficient y)
  hIndependent (simplex_cube_barycentric_sum x) (simplex_cube_barycentric_sum y) hImage.
have hCoefficientValues i:simplex_cube_barycentric_coefficient x i=
    simplex_cube_barycentric_coefficient y i:=congr1 (fun t=>t i) hCoefficients.
have hPrefixes:=@simplex_cube_barycentric_prefix_unique R m x y hCoefficientValues.
apply/ffunP=>i.
have hIndex:Ordinal (ltn_ord i)= i by apply:val_inj;by [].
have hNext:=hPrefixes (val i).+1 (ltn_ord i).
rewrite (@simplex_cube_prefix_successor R m x (val i) (ltn_ord i))
  (@simplex_cube_prefix_successor R m y (val i) (ltn_ord i))
  hIndex (hPrefixes (val i) (ltnW (ltn_ord i))) in hNext.
exact:(mulIf (lt0r_neq0 (@simplex_cube_prefix_positive R m y (val i) hY)) hNext).
Qed.
