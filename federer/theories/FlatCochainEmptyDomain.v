(** Federer (1969), 4.1.19, p. 377: retain
    the empty-open endpoint of the cochain definition
    and its literal global-comass formula. The original
    flat union and cochain then contain only zero;
    the old empty global supremum remains minus infinity. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentSupportExtensionality SmoothCompactSet FlatCurrentFinite
  FlatCurrentUnionSpace FlatCochainSpace FlatCochainNormLaws
  LinearSubspaceRepresentationUP CurrentGlobalComassSealed
  CurrentGlobalComassWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EmptyDomain.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hEmpty : forall x, ~U x.
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation F := (@flat_cochain_norm R h2 n m U hU).

(** Source for [flat_current_union_empty_domain_zero]: the
    empty original F_m(U) carrier is the zero
    vector space, supporting all endpoints of the
    definition in Federer 4.1.19, p. 377.
    Each actual member's own compact index suffices. *)
Theorem flat_current_union_empty_domain_zero (T : W) : T=0.
Proof.
have [K hFlat] := @flat_current_union_inclusion_member R h2 n m U hU T.
have hSupport := @flat_current_supported_support R h2 n m U hU K (inc T) hFlat.
have hZero : inc T=0.
  apply: (@current_empty_support_iff_zero R h2 n m U hU (inc T)).1=> x hx.
  exact: (@hEmpty x (smooth_compact_in_domain K x (hSupport x hx))).
apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
by rewrite hZero linear0.
Qed.

(** Source for [flat_cochain_empty_domain_zero]: the
    only original flat cochain on empty U
    is zero, supporting Federer 4.1.19,
    p. 377. No nonzero-space assumption is
    inserted into the definition of a cochain. *)
Theorem flat_cochain_empty_domain_zero (alpha : A) : alpha=0.
Proof.
apply: (subspace_representation_injective
  (@flat_cochain_space_laws R h2 n m U hU)).
apply: hom_ext=> T; rewrite linear0 hom_zeroE.
by rewrite (flat_current_union_empty_domain_zero T) linear0.
Qed.

(** Source for [flat_cochain_empty_domain_norm_zero]: the
    least nonnegative common bound on empty U
    is zero, supporting the norm convention in
    Federer 4.1.19, p. 377. *)
Theorem flat_cochain_empty_domain_norm_zero (alpha : A) : F alpha=0.
Proof.
rewrite (flat_cochain_empty_domain_zero alpha).
exact: (real_seminorm_zero (@flat_cochain_norm_is_norm R h2 n m U hU).1).
Qed.

(** Source for [flat_cochain_empty_domain_global_comass]: the
    original literal supremum on empty U is
    minus infinity in either degree. Adjoining the
    nonnegative norm threshold gives the zero norm
    at this endpoint of Federer 4.1.19, p. 377. *)
Theorem flat_cochain_empty_domain_global_comass (alpha : A)
    (phi : X -> A_m X R^o m) (psi : X -> A_m X R^o m.+1) :
  (F alpha)%:E=Order.max 0%E
    (Order.max (@CurrentGlobalComass.value R h2 n m U phi)
      (@CurrentGlobalComass.value R h2 n m.+1 U psi)).
Proof.
have hUZero : U=set0.
  apply: funext=> x; apply: propext; split.
  - move=> hx; exact: (@hEmpty x hx).
  - by [].
have hPhi : @CurrentGlobalComass.value R h2 n m U phi=-oo%E.
  by rewrite hUZero current_global_comass_empty_value.
have hPsi : @CurrentGlobalComass.value R h2 n m.+1 U psi=-oo%E.
  by rewrite hUZero current_global_comass_empty_value.
by rewrite flat_cochain_empty_domain_norm_zero hPhi hPsi maxxx maxeNy.
Qed.
End EmptyDomain.
