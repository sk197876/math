(** Federer (1969), 1.7.5, p. 33: public covector inner product and norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity
  ExteriorNorm ExteriorCovectorInnerUP ExteriorCovectorInnerSealed
  LinearBasis ExteriorGrading AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Interface.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.

(** Source for [exterior_covector_inner]: Federer 1.7.5,
    p. 33, the inner product on m-covectors supplied by its
    sealed characterising specification. *)
Definition exterior_covector_inner := @ExteriorCovectorInner.product R h2 V B hB n e he m.

(** Source for [exterior_covector_innerP]: Federer 1.7.5,
    p. 33, the covector product satisfies its defining laws. *)
Lemma exterior_covector_innerP : is_exterior_covector_inner_product h2 hB exterior_covector_inner.
Proof. exact: ExteriorCovectorInner.laws. Qed.

(** Source for [exterior_covector_inner_productP]: Federer
    1.7.5, p. 33, the specified covector product is an inner product. *)
Lemma exterior_covector_inner_productP : is_inner_product exterior_covector_inner.
Proof. exact: exterior_covector_inner_laws exterior_covector_innerP. Qed.

(** Source for [inner_exterior_form_isometry]: Federer
    1.7.5, p. 33, gamma_m is orthogonal for the induced products. *)
Theorem inner_exterior_form_isometry (x y : exterior_power V m) :
  exterior_covector_inner (inner_exterior_form h2 hB x) (inner_exterior_form h2 hB y) =
    exterior_inner_form h2 hB x y.
Proof. exact (@exterior_covector_inner_isometry R h2 V B hB m
  exterior_covector_inner exterior_covector_innerP x y). Qed.

(** Source for [exterior_covector_norm]: Federer 1.7.5,
    p. 33, the norm associated with the induced covector inner product. *)
Definition exterior_covector_norm := inner_norm exterior_covector_inner_productP.

(** Source for [inner_exterior_form_norm]: Federer 1.7.5,
    p. 33, the orthogonal map gamma_m preserves norms. *)
Theorem inner_exterior_form_norm (x : exterior_power V m) :
  exterior_covector_norm (inner_exterior_form h2 hB x) = exterior_norm h2 hB x.
Proof.
apply: inner_norm_value; first exact: exterior_norm_nonnegative.
by rewrite exterior_norm_square inner_exterior_form_isometry.
Qed.
End Interface.
