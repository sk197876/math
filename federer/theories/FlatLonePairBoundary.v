(** Federer (1969), 4.1.19, p. 377:
    the two original q summands interact
    with the actual flat-current boundary.
    These supporting identities give the pair
    (psi,0) for the coboundary of alpha. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySquared FlatCurrentUnionSpace
  FlatCurrentUnionBoundary CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorLinear
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairFlatUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FlatPairBoundary.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P d := (@current_lone_pair_space R h2 n d U hU).
Local Notation W d := (@flat_current_union_space R h2 n d U hU).
Local Notation O d := (@compact_summable_multivector_space R h2 n d U hU).
Local Notation inc d := (@flat_current_union_inclusion R h2 n d U hU).
Local Notation image d := (@compact_summable_multivector_current R h2 n d U hU).
Local Notation boundary := (@flat_current_union_boundary R h2 n m U hU).
Variable Q : Hom (P m) (W m).
Variable S : Hom (P m.+1) (W m.+1).
Hypothesis hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q.
Hypothesis hS : @is_current_lone_pair_flat_map R h2 n m.+1 U hU S.

(** Source for [flat_lone_pair_density_boundary]:
    boundary of the first q summand
    is the second q summand one degree
    below, supporting the coboundary representation
    in Federer 4.1.19, p. 377.
    The equality is in the original flat union. *)
Theorem flat_lone_pair_density_boundary (eta : O m.+1) :
  boundary (S (eta,0))=Q (0,eta).
Proof.
have hZero d : image d 0=0.
  exact: (lin0 (@compact_summable_multivector_current_linear R h2 n d U hU)).
apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
rewrite flat_current_union_boundary_value (hS (eta,0)) (hQ (0,eta))
  (@CurrentLonePair.laws R h2 n m.+1 U hU (eta,0))
  (@CurrentLonePair.laws R h2 n m U hU (0,eta)) /= !hZero !linear0.
by rewrite addr0 add0r.
Qed.

(** Source for [flat_lone_pair_boundary_squared]:
    boundary of the second q summand
    is zero, supporting the zero second
    density for d alpha in Federer
    4.1.19, p. 377. Only the
    old actual boundary-squared identity is used. *)
Theorem flat_lone_pair_boundary_squared (zeta : O m.+2) :
  boundary (S (0,zeta))=0.
Proof.
have hZero d : image d 0=0.
  exact: (lin0 (@compact_summable_multivector_current_linear R h2 n d U hU)).
apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
rewrite flat_current_union_boundary_value (hS (0,zeta))
  (@CurrentLonePair.laws R h2 n m.+1 U hU (0,zeta)) /= hZero add0r.
by rewrite current_boundary_squared linear0.
Qed.
End FlatPairBoundary.
