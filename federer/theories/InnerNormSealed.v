(** Federer (1969), 1.7.1, p. 28: existence of the associated norm. Scalar
    square roots provide the witness; opaque module ascription exposes only
    its abstract laws. Real-closed scalars suffice here; no completeness or
    finite dimension is assumed. Source context and expanded references:
    InnerNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type InnerNormSig.
(** Source for [norm]: Federer 1.7.1, p. 28, the norm
    associated with an inner product, specified without a construction. *)
Parameter norm : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R), is_inner_product B -> V -> R.
(** Source for [laws]: Federer 1.7.1, p. 28, nonnegative
    square-root laws. The following witness proves this specification. *)
Parameter laws : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B),
  is_inner_norm B (@norm R V B hB).
End InnerNormSig.

Module InnerNorm : InnerNormSig.
(** Source for [norm]: Federer 1.7.1, p. 28, existence
    witness using the scalar square-root operation. *)
Definition norm (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (_ : is_inner_product B) (x : V) : R := Num.sqrt (B x x).
(** Source for [laws]: Federer 1.7.1, p. 28, verification
    that the square-root witness satisfies the norm specification. *)
Lemma laws (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) :
  is_inner_norm B (@norm R V B hB).
Proof.
constructor=> x; first exact: sqrtr_ge0.
by rewrite /norm sqr_sqrtr // (inner_nonnegative hB).
Qed.
End InnerNorm.
