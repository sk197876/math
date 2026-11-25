(** Federer (1969), 4.1.11, pp. 365–366: the original
    product maps used in affine naturality and associativity are
    smooth. Reuse the componentwise map of 3.2.23 and the bounded
    linear composition calculus of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormRegularityLinearMaps NormFiniteLinearBound InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianLinear CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentCartesianMapClass.
Variable R : realType.
Variables m mu n v : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R mu).
Local Notation Z := (R_n R (m+mu)%N).
Local Notation N := (R_n R n).
Local Notation V := (R_n R v).
Local Notation W := (R_n R (n+v)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R mu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+mu)%N)).
Local Notation NN := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NV := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R (n+v)%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY :=
  (inner_norm_real_norm (@euclidean_inner_productP R mu)).
Local Notation hNZ :=
  (inner_norm_real_norm (@euclidean_inner_productP R (m+mu)%N)).
Local Notation hNN :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNV :=
  (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNW :=
  (inner_norm_real_norm (@euclidean_inner_productP R (n+v)%N)).
Local Notation p := (@euclidean_first_block_map R m mu).
Local Notation q := (@euclidean_last_block_map R m mu).
Local Notation left := (@euclidean_first_injection_map R n v).
Local Notation right := (@euclidean_last_injection_map R n v).
Variables (f : X -> N) (g : Y -> V).
Hypothesis hf : norm_class_all_orders hNX hNN (fun _ => True) f.
Hypothesis hg : norm_class_all_orders hNY hNV (fun _ => True) g.

(** Source for [current_cartesian_map_smooth]: the preceding
    componentwise map f times g is smooth when its two maps are
    smooth on their Euclidean spaces, supporting the original
    globally polynomial maps in Federer 4.1.11, pp. 365–366.
    No properness of either map is assumed. *)
Theorem current_cartesian_map_smooth :
  norm_class_all_orders hNZ hNW (fun _ => True)
    (@euclidean_cartesian_map R m mu n v f g).
Proof.
have hp := @norm_finite_linear_bounded R Z X NZ NX hNZ hNX
  (m+mu)%N (@coordinate_basis R (m+mu)%N)
  (@coordinate_basisP R (m+mu)%N) p.
have hq := @norm_finite_linear_bounded R Z Y NZ NY hNZ hNY
  (m+mu)%N (@coordinate_basis R (m+mu)%N)
  (@coordinate_basisP R (m+mu)%N) q.
have hLeft := @norm_finite_linear_bounded R N W NN NW hNN hNW
  n (@coordinate_basis R n) (@coordinate_basisP R n) left.
have hRight := @norm_finite_linear_bounded R V W NV NW hNV hNW
  v (@coordinate_basis R v) (@coordinate_basisP R v) right.
move=> k.
have hFirst := @norm_class_precompose_linear R Z X N NZ NX NN
  hNZ hNX hNN (fun _ => True) f p k hp (hf k).
have hSecond := @norm_class_precompose_linear R Z Y V NZ NY NV
  hNZ hNY hNV (fun _ => True) g q k hq (hg k).
have hFirstImage := @norm_class_postcompose_linear R Z N W NZ NN NW
  hNZ hNN hNW (fun _ => True) (fun z => f (p z)) left k hLeft hFirst.
have hSecondImage := @norm_class_postcompose_linear R Z V W NZ NV NW
  hNZ hNV hNW (fun _ => True) (fun z => g (q z)) right k hRight hSecond.
apply: (norm_class_domain_agreement _ (norm_class_add hFirstImage hSecondImage)).
move=> z _.
symmetry.
change (@euclidean_cartesian_map R m mu n v f g z =
  @euclidean_first_injection R n v (f (p z)) +
  @euclidean_last_injection R n v (g (q z))).
exact: euclidean_block_join_sum.
Qed.

(** Source for [current_cartesian_map_on_open_product_smooth]:
    restrict the preceding globally smooth map to its original
    open product source, supporting Federer 4.1.11, pp. 365–366.
    The factor domains and empty or zero-dimensional blocks remain. *)
Theorem current_cartesian_map_on_open_product_smooth
    (A : set X) (B : set Y)
    (hA : forall x, A x -> norm_domain_interior NX A x)
    (hB : forall y, B y -> norm_domain_interior NY B y) :
  norm_class_all_orders hNZ hNW (@euclidean_cartesian_set R m mu A B)
    (@euclidean_cartesian_map R m mu n v f g).
Proof.
move=> k.
exact: (@norm_class_open_restriction R Z W NZ NW hNZ hNW
  (fun _ => True) (@euclidean_cartesian_set R m mu A B)
  (@euclidean_cartesian_map R m mu n v f g) k (fun _ _ => Logic.I)
  (@current_cartesian_domain_open R m mu A B hA hB)
  (current_cartesian_map_smooth k)).
Qed.
End CurrentCartesianMapClass.

(** Source for [current_cartesian_map_domain_image]: the
    original componentwise map preserves the indicated product
    domains when its factors do, supporting Federer 4.1.11,
    pp. 365–366, by 3.2.23, p. 260. *)
Definition current_cartesian_map_domain_image
    (R : realType) (m mu n v : nat)
    (A : set (R_n R m)) (B : set (R_n R mu))
    (C : set (R_n R n)) (D : set (R_n R v))
    (f : R_n R m -> R_n R n) (g : R_n R mu -> R_n R v)
    (hF : forall x, A x -> C (f x))
    (hG : forall y, B y -> D (g y)) :
  forall z, @euclidean_cartesian_set R m mu A B z ->
    @euclidean_cartesian_set R n v C D
      (@euclidean_cartesian_map R m mu n v f g z).
Proof.
move=> z hz.
change (C ((@euclidean_block_split R n v
    (@euclidean_cartesian_map R m mu n v f g z)).1) /\
  D ((@euclidean_block_split R n v
    (@euclidean_cartesian_map R m mu n v f g z)).2)).
rewrite euclidean_cartesian_map_coordinates.
exact: conj (hF _ hz.1) (hG _ hz.2).
Defined.
