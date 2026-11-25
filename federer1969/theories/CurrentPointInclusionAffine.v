(** Federer (1969), 4.1.11, p. 366: the two
    endpoint inclusions of a simplicial prism are affine.
    Reuse the original block injections and the affine
    decomposition of 2.7.16, p. 134. No new chosen
    map or coordinate space is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom AffineMaps RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianSwap EuclideanCartesianSwapLinear CurrentCartesianAffineSlice
  CurrentCartesianPointInclusion CurrentCompactRightPointProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_point_inclusion_affine]: the
    original map u mapped to (a,u) is affine,
    supporting the upper and lower prism faces in
    Federer 4.1.11, p. 366. *)
Theorem current_point_inclusion_affine (R:realType) m n (a:R_n R m):
  is_affine_map (@current_cartesian_point_inclusion R m n a).
Proof.
pose P:=@euclidean_first_injection_map R m n.
pose Q:=@euclidean_last_injection_map R m n.
have hValues:current_cartesian_point_inclusion a=
    (fun x:R_n R n=>(P a:R_n R (m+n)%N)+(Q x:R_n R (m+n)%N)).
  apply:funext=>x;exact:current_cartesian_join_affine.
rewrite hValues.
case:(@affine_isomorphism R (R_n R n) (R_n R (m+n)%N) (hom_as_linear Q) (P a))=>hA _ _ _;exact:hA.
Qed.

(** Source for [current_right_point_inclusion_values]: the
    existing right endpoint inclusion has its literal
    original values (x,b), supporting Federer 4.1.11,
    p. 366. *)
Theorem current_right_point_inclusion_values (R:realType) m n (b:R_n R n) (x:R_n R m):
  @current_cartesian_right_point_inclusion R m n b x=@euclidean_block_join R m n (x,b).
Proof.
change (@euclidean_cartesian_swap R n m (@euclidean_block_join R n m (b,x))=
  @euclidean_block_join R m n (x,b)).
by rewrite /euclidean_cartesian_swap euclidean_block_joinK.
Qed.

(** Source for [current_right_point_inclusion_affine]: the
    original map x mapped to (x,b) is affine,
    supporting the zero-dimensional prism endpoint in
    Federer 4.1.11, p. 366. *)
Theorem current_right_point_inclusion_affine (R:realType) m n (b:R_n R n):
  is_affine_map (@current_cartesian_right_point_inclusion R m n b).
Proof.
pose P:=@euclidean_first_injection_map R m n.
pose Q:=@euclidean_last_injection_map R m n.
have hValues:current_cartesian_right_point_inclusion b=
    (fun x:R_n R m=>(Q b:R_n R (m+n)%N)+(P x:R_n R (m+n)%N)).
  apply:funext=>x;by rewrite current_right_point_inclusion_values current_cartesian_join_affine addrC.
rewrite hValues.
case:(@affine_isomorphism R (R_n R m) (R_n R (m+n)%N) (hom_as_linear P) (Q b))=>hA _ _ _;exact:hA.
Qed.
