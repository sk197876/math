(** Federer (1969), 4.1.6, p. 352: existence
    of the exact partial exterior derivative, from
    its independent graph specification and the proved
    uniqueness of actual norm differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AlternatingForms PartialFunctionUP ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [exterior_derivative_graph_witness]: the
    original signed derivative relation is single-valued,
    Federer 4.1.6, p. 352. This witness
    only proves existence; it is sealed separately. *)
Definition exterior_derivative_graph_witness (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi:V->A_m V W m):partial_function V (A_m V W m.+1).
Proof.
refine (@Build_partial_function V (A_m V W m.+1)
  (@has_exterior_derivative R V W NV m NP U phi) _).
move=>a b c hb hc.
exact:(@exterior_derivative_unique R V W NV hNV m NP hNP U phi a b c hb hc).
Defined.

(** Source for [exterior_derivative_graph_exists]: existence
    of the original partial operator,
    Federer 4.1.6, p. 352, without
    assigning values at nondifferentiable points. *)
Theorem exterior_derivative_graph_exists (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi:V->A_m V W m):
  exists D,is_exterior_derivative_graph NV NP U phi D.
Proof. exists (exterior_derivative_graph_witness hNV hNP U phi)=>a b; by []. Qed.
