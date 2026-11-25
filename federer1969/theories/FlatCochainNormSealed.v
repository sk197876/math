(** Federer (1969), 4.1.19, p. 377: opaque
    selection of the proved least common bound.
    Consumers use only its independent norm laws,
    not the infimum used in the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FlatCurrentUnionSpace FlatCochainUP FlatCochainNormExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type FlatCochainNormSignature.
(** Source for [value]: the original least nonnegative
    cochain bound F(alpha), Federer 4.1.19, p. 377. *)
Parameter value : forall (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : Hom (@flat_current_union_space R h2 n m U hU) R^o),
  @is_flat_cochain R h2 n m U hU alpha -> R.
(** Source for [laws]: the value has the original
    independent least-bound laws of Federer 4.1.19,
    p. 377, with every compact index retained. *)
Parameter laws : forall (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : Hom (@flat_current_union_space R h2 n m U hU) R^o)
    (hAlpha : @is_flat_cochain R h2 n m U hU alpha),
  @is_flat_cochain_norm R h2 n m U hU alpha
    (@value R h2 n m U hU alpha hAlpha).
End FlatCochainNormSignature.

Module FlatCochainNorm : FlatCochainNormSignature.
(** Source for [value]: select the proved existence
    witness for F(alpha), Federer 4.1.19, p. 377. *)
Definition value (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : Hom (@flat_current_union_space R h2 n m U hU) R^o)
    (hAlpha : @is_flat_cochain R h2 n m U hU alpha) : R :=
  projT1 (cid (@flat_cochain_norm_exists R h2 n m U hU alpha hAlpha)).
(** Source for [laws]: the opaque value satisfies
    the proved independent laws, Federer 4.1.19,
    p. 377. No mathematical axiom is added. *)
Lemma laws (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : Hom (@flat_current_union_space R h2 n m U hU) R^o)
    (hAlpha : @is_flat_cochain R h2 n m U hU alpha) :
  @is_flat_cochain_norm R h2 n m U hU alpha
    (@value R h2 n m U hU alpha hAlpha).
Proof.
exact: (projT2 (cid
  (@flat_cochain_norm_exists R h2 n m U hU alpha hAlpha))).
Qed.
End FlatCochainNorm.
