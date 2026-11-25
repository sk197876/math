(** Federer (1969), 4.1.19, p. 377: the
    cochain coboundary uses the original boundary
    on the whole flat-current union. The old
    compact-index boundary theorem gives its range;
    opaque corestriction preserves every actual current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySquared FlatCurrentsUP
  FlatCurrentUnion CurrentLocallyFlatBoundary FlatCurrentUnionSpace
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Boundary.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation A := (@flat_current_union_space R h2 n m U hU).
Local Notation B := (@flat_current_union_space R h2 n m.+1 U hU).
Local Notation incA := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation incB := (@flat_current_union_inclusion R h2 n m.+1 U hU).
Local Notation hA := (@flat_current_union_space_laws R h2 n m U hU).
Local Notation S := (@flat_current_union_subspace R h2 n m U hU).
Local Notation raw :=
  (hom_comp (@current_boundary R h2 n m U hU) incB).

(** Source for [flat_current_union_boundary_range]: the
    original compact-index union is closed under
    boundary by 4.1.12, p. 368, supporting
    the definition of d alpha in Federer
    4.1.19, p. 377. No mass hypothesis is needed. *)
Lemma flat_current_union_boundary_range (T : B) : S (raw T).
Proof.
rewrite hom_compE.
exact: (@flat_current_boundary R h2 n m U hU (incB T)
  (@flat_current_union_inclusion_member R h2 n m.+1 U hU T)).
Qed.

(** Source for [flat_current_union_boundary]: the
    actual boundary map used in Federer 4.1.19,
    p. 377, on the original compact-index
    union. The existing opaque corestriction is
    applied to its already proved flat range. *)
Definition flat_current_union_boundary : Hom B A :=
  @LinearSubspaceLift.map R B A C S incA hA raw
    flat_current_union_boundary_range.

(** Source for [flat_current_union_boundary_value]:
    corestriction preserves the literal current boundary,
    supporting d alpha(S)=alpha(boundary S) in
    Federer 4.1.19, p. 377. *)
Theorem flat_current_union_boundary_value (T : B) :
  incA (flat_current_union_boundary T) =
    @current_boundary R h2 n m U hU (incB T).
Proof.
exact: (@LinearSubspaceLift.evaluation R B A C S incA hA raw
  flat_current_union_boundary_range T).
Qed.
End Boundary.

(** Source for [flat_current_union_boundary_squared]:
    boundary squared remains zero on the actual
    full flat-current carriers, supporting d squared
    zero in Federer 4.1.19, p. 377.
    The old current identity proves the result. *)
Theorem flat_current_union_boundary_squared
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T : @flat_current_union_space R h2 n m.+2 U hU) :
  @flat_current_union_boundary R h2 n m U hU
    (@flat_current_union_boundary R h2 n m.+1 U hU T) = 0.
Proof.
apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
by rewrite !flat_current_union_boundary_value current_boundary_squared linear0.
Qed.
