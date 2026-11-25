(** Federer (1969), 4.1.6, p. 354: existence
    of the exact original partial pullback graph.
    The independent characteristic relation and proved
    uniqueness supply a witness before it is sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import RealNormUP AlternatingForms PartialFunctionUP DifferentialFormPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [differential_form_pullback_exists]: the
    original pullback exists as a partial function,
    Federer 4.1.6, p. 354, for arbitrary
    coefficient vector spaces and every degree. *)
Theorem differential_form_pullback_exists (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi:Y->A_m Y W m):
  exists P,is_differential_form_pullback_graph NX NY A B f phi P.
Proof.
have hUnique:forall a b c,has_differential_form_pullback NX NY A B f phi a b->
    has_differential_form_pullback NX NY A B f phi a c->b=c.
  move=>a b c; exact:(@differential_form_pullback_unique R X Y W NX NY hNX hNY A B f m phi a b c).
exists (@Build_partial_function X (A_m X W m)
  (@has_differential_form_pullback R X Y W NX NY A B f m phi) hUnique)=>a b.
by [].
Qed.
