(** Federer (1969), 1.7.5, p. 33: the pairing bound and its complete
    equality criterion. Finite dimension is used only to represent every
    covector by gamma. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorIsomorphism
  ExteriorCovectorInner ExteriorNorm InnerNormInequalities InnerCauchyEquality
  IndependentPair LinearBasis ExteriorGrading AlternatingCoordinates AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Pairing.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Local Notation D := (@exterior_covector_inner R h2 V B hB n e he m).
Local Notation N := (@exterior_covector_norm R h2 V B hB n e he m).

(** Source for [exterior_pairing_inner]: Federer 1.7.5,
    p. 33, supporting identification of the pairing with the
    covector inner product after applying gamma to the multivector. *)
Lemma exterior_pairing_inner (x : exterior_power V m) (a : A_m V R^o m) :
  pairing x a = D (inner_exterior_form h2 hB x) a.
Proof.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
rewrite -(hgf a) inner_exterior_form_isometry; reflexivity.
Qed.

(** Source for [exterior_pairing_bound]: Federer 1.7.5,
    p. 33, absolute pairing is bounded by the product of the
    multivector norm and the induced covector norm. *)
Theorem exterior_pairing_bound (x : exterior_power V m) (a : A_m V R^o m) :
  `|pairing x a| <= exterior_norm h2 hB x * N a.
Proof.
rewrite exterior_pairing_inner.
have hh := @inner_cauchy R (A_m V R^o m) D
  (@exterior_covector_inner_productP R h2 V B hB n e he m)
  (inner_exterior_form h2 hB x) a.
by rewrite -(@inner_exterior_form_norm R h2 V B hB n e he m x); exact hh.
Qed.

(** Source for [exterior_pairing_equality]: Federer 1.7.5,
    p. 33, equality in the pairing bound holds exactly when
    gamma_m(x) and the covector are linearly dependent, including zero. *)
Theorem exterior_pairing_equality (x : exterior_power V m) (a : A_m V R^o m) :
  `|pairing x a| = exterior_norm h2 hB x * N a <->
    ~ independent_pair (inner_exterior_form h2 hB x) a.
Proof.
rewrite exterior_pairing_inner -(@inner_exterior_form_norm R h2 V B hB n e he m x).
exact: inner_cauchy_equality_dependent.
Qed.
End Pairing.
