(** Federer (1969), 4.1.6, p. 352: the original
    partial exterior derivative behind an opaque graph
    interface. Its specification and existence precede
    the selection. Consumers use only the graph laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AlternatingForms PartialFunctionUP
  ExteriorDerivativeUP ExteriorDerivativeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ExteriorDerivativeSignature.
(** Source for [value]: the original partial d phi,
    Federer 4.1.6, p. 352. *)
Parameter value:forall (R:realType) (V W:lmodType R)
  (NV:V->R),is_real_norm NV ->forall m (NP:A_m V W m->R),is_real_norm NP ->
  (V->Prop)->(V->A_m V W m)->partial_function V (A_m V W m.+1).
(** Source for [laws]: the exact signed graph,
    Federer 4.1.6, p. 352. *)
Parameter laws:forall (R:realType) (V W:lmodType R)
  (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
  (U:V->Prop) (phi:V->A_m V W m),
  is_exterior_derivative_graph NV NP U phi (@value R V W NV hNV m NP hNP U phi).
End ExteriorDerivativeSignature.
Module ExteriorDerivative:ExteriorDerivativeSignature.
(** Source for [value]: select the already proved
    partial derivative graph,
    Federer 4.1.6, p. 352. *)
Definition value (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi:V->A_m V W m):partial_function V (A_m V W m.+1):=
  projT1 (cid (@exterior_derivative_graph_exists R V W NV hNV m NP hNP U phi)).
(** Source for [laws]: every graph pair has exactly
    the original defining property,
    Federer 4.1.6, p. 352. *)
Lemma laws (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi:V->A_m V W m):
  is_exterior_derivative_graph NV NP U phi (@value R V W NV hNV m NP hNP U phi).
Proof. exact:(projT2 (cid (@exterior_derivative_graph_exists R V W NV hNV m NP hNP U phi))). Qed.
End ExteriorDerivative.
