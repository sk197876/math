(** Federer (1969), 2.4.12, pp. 87–88: the canonical map tau from Y into Y**
    is characterised by evaluation. Those examples do not supply the norm
    claims. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_bidual_embedding]: the displayed identity
    (alpha,tau(y)) = (y,alpha) in Federer 2.4.12, p. 87.
    This law specifies the map; existence and isometry are proved separately. *)
Definition is_bidual_embedding (R : fieldType) (V D B : lmodType R)
    (evaluationD : Hom D (Hom V R^o))
    (evaluationB : Hom B (Hom D R^o)) (tau : Hom V B) : Prop :=
  forall y a, evaluationB (tau y) a = evaluationD a y.

(** Source for [is_reflexive_embedding]: reflexivity as surjectivity
    of the canonical map, Federer 2.4.12, p. 88, final parenthesis.
    The separate embedding law identifies which map is meant. *)
Definition is_reflexive_embedding (R : fieldType) (V B : lmodType R)
    (tau : Hom V B) : Prop := forall b : B, exists y : V, tau y = b.
