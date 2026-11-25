(** Federer (1969), 4.1.6, p. 354: independent
    graph specification of the original pullback.
    At a, use the actual Df(a) and the original
    contravariant map on forms from 1.4.1. The
    target-domain condition is retained explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  Alternating PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [has_differential_form_pullback]: the
    displayed defining formula for f# phi in
    Federer 4.1.6, p. 354. No value
    outside the original differentiability and target
    domains is assigned. *)
Definition has_differential_form_pullback (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (A:X->Prop) (B:Y->Prop)
    (f:X->Y) m (phi:Y->A_m Y W m) a (b:A_m X W m):Prop:=
  B (f a) /\ exists L:Hom X Y,has_norm_differential NX NY A f a L /\
    b=A_m_dual (hom_as_linear L) (phi (f a)).

(** Source for [is_differential_form_pullback_graph]: the
    exact original partial pullback operation,
    Federer 4.1.6, p. 354. *)
Definition is_differential_form_pullback_graph (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (A:X->Prop) (B:Y->Prop)
    (f:X->Y) m (phi:Y->A_m Y W m) (P:partial_function X (A_m X W m)):Prop:=
  forall a b,partial_function_graph P a b <->
    has_differential_form_pullback NX NY A B f phi a b.

(** Source for [differential_form_pullback_unique]:
    the original pullback is well-defined, Federer
    4.1.6, p. 354, by uniqueness of the
    actual first differential. *)
Lemma differential_form_pullback_unique (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi:Y->A_m Y W m) a b c:
  has_differential_form_pullback NX NY A B f phi a b->
  has_differential_form_pullback NX NY A B f phi a c->b=c.
Proof.
move=>[_ [L [hL ->]]] [_ [M [hM ->]]].
by rewrite (norm_differential_unique hNX hNY hL hM).
Qed.
