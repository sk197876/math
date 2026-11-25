(** Federer (1969), 4.1.12, p. 368, used
    in 4.1.14, p. 371: positive-degree
    boundary preserves local flatness. The preceding
    exact point criterion and support nonincrease
    reduce the assertion to the already proved
    compact flat boundary theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySupport FlatCurrentsUP
  FlatCurrentBoundary LocallyFlatPointCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [flat_current_boundary]: boundary preserves
    the original compact-index union, Federer 4.1.12,
    p. 368, supporting 4.1.14, p. 371. *)
Lemma flat_current_boundary (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m.+1):
  @is_flat_current R h2 n m.+1 U hU T->
  @is_flat_current R h2 n m U hU (@current_boundary R h2 n m U hU T).
Proof.
move=>[K hK];exists K;exact:(@flat_current_boundary_supported R h2 n m U hU K T hK).
Qed.

(** Source for [locally_flat_current_boundary]: the
    original locally flat boundary stability, Federer
    4.1.12, p. 368, supporting the Lipschitz
    homotopy identities in 4.1.14, p. 371.
    No normality or finite-mass premise is added. *)
Theorem locally_flat_current_boundary (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m.+1):
  @is_locally_flat_current R h2 n m.+1 U hU T->
  @is_locally_flat_current R h2 n m U hU (@current_boundary R h2 n m U hU T).
Proof.
move=>hT.
apply:(@locally_flat_point_criterion R h2 n m U hU
  (@current_boundary R h2 n m U hU T)).2=>x hx.
have[S [hS hNear]]:=(@locally_flat_point_criterion R h2 n m.+1 U hU T).1 hT x hx.
exists (@current_boundary R h2 n m U hU S);split.
- exact:(@flat_current_boundary R h2 n m U hU S hS).
rewrite -(linB (hom_linear (@current_boundary R h2 n m U hU))).
move=>hSupport;apply:hNear.
exact:(@current_boundary_support_subset R h2 n m U hU (T-S) x hSupport).
Qed.
