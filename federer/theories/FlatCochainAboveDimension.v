(** Federer (1969), 4.1.19, p. 377: the
    original cochain definition and least nonnegative bound
    retain exterior degrees above the ambient dimension.
    The earlier actual current-space vanishing theorem
    makes both the flat union and its cochain zero. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentAboveDimension FlatCurrentUnionSpace FlatCochainSpace FlatCochainNormLaws
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section AboveDimension.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Hypothesis hDegree : (n<m)%N.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation F := (@flat_cochain_norm R h2 n m U hU).

(** Source for [flat_current_union_above_dimension_zero]:
    the above-dimensional endpoint of the original
    F_m(U) carrier in Federer 4.1.19,
    p. 377, follows from actual current
    vanishing rather than a new premise on members. *)
Theorem flat_current_union_above_dimension_zero (T : W) : T=0.
Proof.
have hZero : inc T=0 := @current_above_dimension R h2 n m hDegree U hU (inc T).
apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
by rewrite hZero linear0.
Qed.

(** Source for [flat_cochain_above_dimension_zero]: the
    only cochain in a degree greater than
    n is zero, supporting every natural degree
    in Federer 4.1.19, p. 377. *)
Theorem flat_cochain_above_dimension_zero (alpha : A) : alpha=0.
Proof.
apply: (subspace_representation_injective (@flat_cochain_space_laws R h2 n m U hU)).
apply: hom_ext=> T; rewrite linear0 hom_zeroE.
by rewrite (flat_current_union_above_dimension_zero T) linear0.
Qed.

(** Source for [flat_cochain_above_dimension_norm_zero]: the
    actual least nonnegative cochain norm is zero
    at this zero-space endpoint of Federer
    4.1.19, p. 377. *)
Theorem flat_cochain_above_dimension_norm_zero (alpha : A) : F alpha=0.
Proof.
rewrite (flat_cochain_above_dimension_zero alpha).
exact: (real_seminorm_zero (@flat_cochain_norm_is_norm R h2 n m U hU).1).
Qed.
End AboveDimension.
