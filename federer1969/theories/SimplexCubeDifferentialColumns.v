(** Federer (1969), 4.1.27, p. 384:
    identify every actual D_j f by
    the exact coordinate-line increment. Its expansion
    uses only the consecutive edges with
    index at least j, giving the
    original upper triangular wedge calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  CurrentMapDifferential CurrentClassOneCompactPlateau
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeParametrisationClass SimplexCubePrefixIncrement
  DifferentialExactLineIncrement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_differential_column]: the literal
    coefficient expression for D_j f in
    the wedge differential display of 4.1.27,
    p. 384. It abbreviates finite sums
    of the original consecutive edge vectors. *)
Definition simplex_cube_differential_column (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m) (j:'I_m):R_n R n:=
  \sum_(i:'I_m | (j<=i)%N)
    simplex_cube_omitted_prefix x (val i).+1 j*:
      simplex_consecutive_edge_family v i.

(** Source for [simplex_cube_parametrisation_coordinate_increment]: the
    full original polynomial has the exact
    affine coordinate increment used to compute
    D_j f in 4.1.27, p. 384.
    No division by a coordinate occurs. *)
Theorem simplex_cube_parametrisation_coordinate_increment (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m) (j:'I_m) (h:R):
  @SimplexCubeParametrisation.value R n m v
    (x+h*:@coordinate_basis R m j)-
    @SimplexCubeParametrisation.value R n m v x=
      h*:simplex_cube_differential_column v x j.
Proof.
rewrite !SimplexCubeParametrisation.laws opprD addrACA subrr add0r -sumrB.
rewrite /simplex_cube_differential_column scaler_sumr [RHS]big_mkcond.
apply:eq_bigr=>i _.
rewrite -scalerBl simplex_cube_prefix_coordinate_increment ltnS.
case hJI:(j<=i)%N.
- by rewrite scalerA.
- by rewrite mulr0 scale0r.
Qed.

(** Source for [simplex_cube_map_differential_column]: the actual
    differential of the opaque original map
    has exactly the displayed coordinate columns,
    supporting 4.1.27, p. 384. Smoothness derives
    differentiability at every original point, including
    those on zero-coordinate hyperplanes. *)
Theorem simplex_cube_map_differential_column (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m) (j:'I_m):
  @current_map_differential R m n (fun _=>True)
    (@SimplexCubeParametrisation.value R n m v) x
      (@coordinate_basis R m j)=simplex_cube_differential_column v x j.
Proof.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose f:=@SimplexCubeParametrisation.value R n m v.
have hFirst:norm_class_one NX NY (fun _=>True) f:=
  (@norm_class_firstP R (R_n R m) (R_n R n) NX NY hNX hNY
    (fun _=>True) f).1 (@simplex_cube_parametrisation_smooth R n m v 1%N).
have hD:=@current_class_one_map_differential_actual R m n (fun _=>True) f hFirst x Logic.I.
apply:(@norm_differential_exact_line_increment R (R_n R m) (R_n R n)
  NX NY hNX hNY (fun _=>True) f x (@current_map_differential R m n
    (fun _=>True) f x) (@coordinate_basis R m j)
    (simplex_cube_differential_column v x j) hD).
exact:simplex_cube_parametrisation_coordinate_increment.
Qed.
