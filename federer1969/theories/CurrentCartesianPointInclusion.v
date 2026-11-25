(** Federer (1969), 4.1.8, p. 362: the
    original affine inclusion epsilon_z(y)=(z,y).
    It uses the existing Cartesian block map and
    has exactly the original second injection Q
    as differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianAffineSlice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianPointInclusion.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).

(** Source for [current_cartesian_point_inclusion]: the
    original derived affine map epsilon_z(y)=(z,y),
    Federer 4.1.8, p. 362, using the original
    Euclidean Cartesian identification. *)
Definition current_cartesian_point_inclusion (z:X) (y:Y):Z:=euclidean_block_join (z,y).

(** Source for [current_cartesian_point_inclusion_image]: the
    original inclusion maps B to A times B when z
    belongs to A, supporting Federer 4.1.8, p. 362. *)
Lemma current_cartesian_point_inclusion_image (A:set X) (B:set Y) z:
  A z->forall y,B y->euclidean_cartesian_set A B (current_cartesian_point_inclusion z y).
Proof.
move=>hz y hy.
change (A (euclidean_block_split (euclidean_block_join (z,y))).1 /\
  B (euclidean_block_split (euclidean_block_join (z,y))).2).
by rewrite euclidean_block_joinK;split.
Qed.

(** Source for [current_cartesian_point_inclusion_left_inverse]:
    q composed with the original point inclusion is
    the identity, supporting properness in Federer
    4.1.8, p. 362. *)
Lemma current_cartesian_point_inclusion_left_inverse z y:
  @euclidean_last_block_map R m n (current_cartesian_point_inclusion z y)=y.
Proof.
change ((euclidean_block_split (euclidean_block_join (z,y))).2=y).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [current_cartesian_point_inclusion_smooth]: the
    original point inclusion is smooth on every original
    open B, supporting Federer 4.1.8, p. 362,
    by the constant and linear calculus of 3.1.11. *)
Theorem current_cartesian_point_inclusion_smooth (B:set Y)
    (hB:forall y,B y->norm_domain_interior NY B y) (z:X):
  norm_class_all_orders hNY hNZ B (current_cartesian_point_inclusion z).
Proof.
have hFun:current_cartesian_point_inclusion z=(fun y:Y=>(P z:Z)+(Q y:Z)).
  apply:funext=>y;exact:current_cartesian_join_affine.
have hQ:=@norm_finite_linear_bounded R Y Z NY NZ hNY hNZ n
  (@coordinate_basis R n) (@coordinate_basisP R n) Q.
move=>k;rewrite hFun.
apply:(@norm_class_add R Y Z NY NZ hNY hNZ B (fun _=>P z) Q k).
- exact:(@norm_class_constant R Y Z NY NZ hNY hNZ B (P z) k hB).
- exact:(@norm_class_linear R Y Z NY NZ hNY hNZ B Q k hB hQ).
Qed.

(** Source for [current_cartesian_point_inclusion_differential]:
    the actual differential of epsilon_z is Q,
    supporting Federer 4.1.8, p. 362. *)
Theorem current_cartesian_point_inclusion_differential (B:set Y)
    (hB:forall y,B y->norm_domain_interior NY B y) (z:X) y:
  B y->has_norm_differential NY NZ B (current_cartesian_point_inclusion z) y Q.
Proof.
move=>hy.
have hFun:current_cartesian_point_inclusion z=(fun y:Y=>(P z:Z)+(Q y:Z)).
  apply:funext=>s;exact:current_cartesian_join_affine.
have hQ:=@norm_finite_linear_bounded R Y Z NY NZ hNY hNZ n
  (@coordinate_basis R n) (@coordinate_basisP R n) Q.
have hLinear:=@norm_differential_linear R Y Z NY NZ hNY hNZ B y Q (@hB y hy) hQ.
have hConstant:=@norm_differential_constant R Y Z NY NZ hNY hNZ B y (P z) (@hB y hy).
have hSum:=@norm_differential_add R Y Z NY NZ hNZ B (fun _=>P z) Q y 0 Q hConstant hLinear.
rewrite add0r in hSum;rewrite hFun;exact:hSum.
Qed.
End CurrentCartesianPointInclusion.
