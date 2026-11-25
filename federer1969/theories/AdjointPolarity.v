(** Federer (1969), 1.7.4, p. 30: the defining commutative diagram for
    adjoints. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity AdjointUP
  AlternatingCoordinates AlternatingDual OneFormLinear Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [adjoint_polarity_diagram]: Federer 1.7.4,
    p. 30, equivalence between the commutative polarity diagram
    and the displayed inner-product condition defining f*. *)
Theorem adjoint_polarity_diagram (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (a : {linear U -> V}) :
  is_adjoint B C f a <-> forall y,
    inner_polarity hB (a y) = A_m_dual f (inner_polarity hC y).
Proof.
have hm x : map_tuple f [tuple x] = [tuple f x] by apply: val_inj.
split.
- move=> ha y; apply: one_hom_injective; apply: hom_ext => x.
  by rewrite !one_homE A_m_dualE hm !inner_polarityE ha.
- move=> hd x y; rewrite -!inner_polarityE hd A_m_dualE hm.
  by [].
Qed.
