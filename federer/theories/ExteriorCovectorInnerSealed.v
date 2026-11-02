(** Federer (1969), 1.7.5, p. 33: the induced inner product on m-covectors,
    with its transport construction sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP LinearBasis AlternatingCoordinates
  ExteriorCovectorInnerUP ExteriorCovectorInnerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type ExteriorCovectorInnerSig.
(** Source for [product]: Federer 1.7.5, p. 33,
    the inner product on m-covectors making gamma_m orthogonal. *)
Parameter product : forall (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R), is_inner_product B ->
    forall n (e : 'I_n -> V), is_basis e ->
    forall m, A_m V R^o m -> A_m V R^o m -> R.
(** Source for [laws]: Federer 1.7.5, p. 33,
    the chosen product satisfies the abstract isometry specification. *)
Parameter laws : forall (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m,
    is_exterior_covector_inner_product h2 hB (@product R h2 V B hB n e he m).
End ExteriorCovectorInnerSig.
Module ExteriorCovectorInner : ExteriorCovectorInnerSig.
(** Source for [product]: Federer 1.7.5, p. 33,
    select the proved covector metric witness and hide the inverse
    used to prove its existence. *)
Definition product (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :=
  sval (constructive_indefinite_description
    (@exterior_covector_inner_exists R h2 V B hB n e he m)).
(** Source for [laws]: Federer 1.7.5, p. 33,
    the selected inner product satisfies its defining laws. *)
Lemma laws (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :
    is_exterior_covector_inner_product h2 hB (@product R h2 V B hB n e he m).
Proof. exact: (svalP (constructive_indefinite_description
  (@exterior_covector_inner_exists R h2 V B hB n e he m))). Qed.
End ExteriorCovectorInner.
