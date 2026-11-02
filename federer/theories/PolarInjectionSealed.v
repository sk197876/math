(** Federer (1969), 1.7.3, p. 30: sealed existence of the injection
    factorisation with the book's prescribed basis values. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies FiniteIndependence LinearBasis PolarFactorisationUP
  PolarInjectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type PolarInjectionSig.
(** Source for [exists_factors]: Federer 1.7.3, p. 30,
    the factorisation and its prescribed values are specified
    without exposing the completion construction. *)
Parameter exists_factors : forall (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V), is_basis e -> orthonormal_family B e ->
    forall u : 'I_n -> U, finite_independent u ->
    forall f : {linear V -> U},
    (forall i j, i != j -> C (f (e i)) (f (e j)) = 0) ->
    exists (g : {linear V -> V}) (h : {linear V -> U}),
      is_injection_factorisation B C f g h /\
      (forall i, g (e i) = inner_norm hC (f (e i)) *: e i) /\
      (forall i, f (e i) != 0 -> h (e i) = inner_normalize hC (f (e i))).
End PolarInjectionSig.
Module PolarInjection : PolarInjectionSig.
(** Source for [exists_factors]: Federer 1.7.3, p. 30,
    the private witness proves the sealed existence specification. *)
Theorem exists_factors (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (u : 'I_n -> U) (hu : finite_independent u) (f : {linear V -> U})
    (hfo : forall i j, i != j -> C (f (e i)) (f (e j)) = 0) :
    exists (g : {linear V -> V}) (h : {linear V -> U}),
      is_injection_factorisation B C f g h /\
      (forall i, g (e i) = inner_norm hC (f (e i)) *: e i) /\
      (forall i, f (e i) != 0 -> h (e i) = inner_normalize hC (f (e i))).
Proof. exact: (@polar_injection_basis_witness R V U B C hB hC n e he ho u hu f hfo). Qed.
End PolarInjection.
