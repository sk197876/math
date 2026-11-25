(** Federer (1969), 1.7.6, p. 33: equality with the norm of the degree-one
    dual map. The proof transports along the original inner-product
    polarity, using only its abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerPolaritySurjection
  InnerDual InnerNorm LinearBasis AdjointUP AdjointPolarity
  AlternatingCoordinates AlternatingDual OperatorNormUP
  OperatorNormTransport OperatorNormAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [form_pullback_linear]: Federer 1.7.6,
    p. 33, the existing covector pullback from 1.4.1, exposed
    with its proved linear structure for use in operator norms. *)
Definition form_pullback_linear (R : fieldType) (V U : lmodType R)
    (f : {linear V -> U}) m : {linear A_m U R^o m -> A_m V R^o m} :=
  GRing.Linear.clone _ _ _ _ (@A_m_dual R V U R^o f m) _.

(** Source for [operator_dual_norm_equal_adjoint]: Federer
    1.7.6, p. 33, ||dual f|| = ||adjoint f||, using the
    dual inner products specified in 1.7.2. *)
Theorem operator_dual_norm_equal_adjoint (R : rcfType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n k (b : 'I_n -> V) (e : 'I_k -> U) (hb : is_basis b) (he : is_basis e)
    (f : {linear V -> U}) (a : {linear U -> V}) (ha : is_adjoint B C f a) L M :
  is_operator_norm hC hB a L ->
  is_operator_norm (inner_dual_productP hC he) (inner_dual_productP hB hb)
    (form_pullback_linear f 1) M -> L = M.
Proof.
apply: (@operator_norm_isometric_transport R U V (A_m U R^o 1) (A_m V R^o 1)
  C B (inner_dual_product hC he) (inner_dual_product hB hb)
  hC hB (inner_dual_productP hC he) (inner_dual_productP hB hb)
  a (form_pullback_linear f 1) (inner_polarity hC)).
- exact: inner_dual_norm_polarity.
- exact: inner_polarity_surjective he.
- move=> x.
  change (inner_dual_norm hB hb (A_m_dual f (inner_polarity hC x)) = inner_norm hB (a x)).
  rewrite -(proj1 (adjoint_polarity_diagram hB hC f a) ha x).
  exact: inner_dual_norm_polarity.
Qed.

(** Source for [operator_dual_norm_equal]: Federer 1.7.6,
    p. 33, ||f|| = ||dual f||, by the adjoint norm identity. *)
Theorem operator_dual_norm_equal (R : rcfType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n k (b : 'I_n -> V) (e : 'I_k -> U) (hb : is_basis b) (he : is_basis e)
    (f : {linear V -> U}) (a : {linear U -> V}) (ha : is_adjoint B C f a) L M N :
  is_operator_norm hB hC f L -> is_operator_norm hC hB a M ->
  is_operator_norm (inner_dual_productP hC he) (inner_dual_productP hB hb)
    (form_pullback_linear f 1) N -> L = N.
Proof.
move=> hL hM hN.
transitivity M; first exact: operator_norm_adjoint_equal ha hL hM.
exact (@operator_dual_norm_equal_adjoint R V U B C hB hC n k b e hb he f a ha M N hM hN).
Qed.
