(** Federer (1969), 1.7.4, p. 30: identities for the chosen adjoint, derived
    from its abstract specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP LinearBasis AdjointUP Adjoint
  AdjointLaws TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_adjoint_double]: Federer 1.7.4, p. 30,
    the double adjoint equals the original map. *)
Theorem inner_adjoint_double (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    m (c : 'I_m -> U) (hc : is_basis c) (f : {linear V -> U}) :
  inner_adjoint hC hB hc (inner_adjoint hB hC hb f) =1 f.
Proof.
apply: (@adjoint_unique R U V C B hC).
- exact: inner_adjointP.
- exact: (@adjoint_reverse R V U B C hB hC f _ (inner_adjointP hB hC hb f)).
Qed.

(** Source for [inner_adjoint_compose]: Federer 1.7.4,
    p. 30, (g composed with f)* equals f* composed with g*. *)
Theorem inner_adjoint_compose (R : rcfType) (V U W : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (D : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) (hD : is_inner_product D)
    n (b : 'I_n -> V) (hb : is_basis b)
    m (c : 'I_m -> U) (hc : is_basis c)
    (f : {linear V -> U}) (g : {linear U -> W}) :
  inner_adjoint hB hD hb (linear_comp g f) =1
    linear_comp (inner_adjoint hB hC hb f) (inner_adjoint hC hD hc g).
Proof.
apply: (@adjoint_unique R V W B D hB).
- exact: inner_adjointP.
- exact: adjoint_composition (inner_adjointP hB hC hb f) (inner_adjointP hC hD hc g).
Qed.
