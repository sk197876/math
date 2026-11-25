(** Federer (1969), 4.1.12, p. 368: a current
    is locally flat if and only if it agrees near
    every domain point with an original flat current.
    Reuse the actual compact scalar cutoffs, flat
    multiplier stability and finite partition argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet SmoothTestSpaces
  CurrentContraction FlatCurrentsUP FlatCurrentUnion FlatCurrentScalarClosure
  LocallyFlatNearPoint CurrentSubspaceLocality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocallyFlatPointCriterion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).

(** Source for [locally_flat_point_criterion]: the
    exact local-flatness equivalence of Federer
    4.1.12, p. 368, with the original support
    of T-S and all points of arbitrary open U.
    The reverse implication uses a finite partition
    on each actual compact scalar test support. *)
Theorem locally_flat_point_criterion (T:C):
  @is_locally_flat_current R h2 n m U hU T <->
    @is_germwise_flat_current R h2 n m U hU T.
Proof.
split;first exact:(@locally_flat_near_point_flat R h2 n m U hU T).
move=>hLocal.
pose A:=@flat_current_union_subspace R h2 n m U hU.
have hStable:forall (gamma:@current_test_space R h2 n U hU 0%N) (S:C),
    A S->A (@current_contraction R h2 n 0%N m U hU
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) S).
  move=>gamma S hS;exact:(@flat_current_scalar_multiplier R h2 n m U hU gamma S hS).
exact:(@current_subspace_germ_localisation R h2 n m U hU A hStable T hLocal).
Qed.
End LocallyFlatPointCriterion.
