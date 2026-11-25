(** Federer (1969), 4.1.7, p. 359:
    the original pullback acts on smooth
    forms before the proper current pushforward
    is defined. Its value law uses
    exactly the independently specified partial
    pullback of 4.1.6, p. 354. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import AlternatingDual Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws DifferentialFormPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SmoothFormPullbackUP.
Variable R:realType.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Variables E F:lmodType R.
Variables (ev:E->Y->A_m Y R^o m) (fv:F->X->A_m X R^o m).
Variable f:X->Y.

(** Source for [is_smooth_form_pullback]:
    the actual smooth pullback satisfies
    the original partial pullback graph
    at every original domain point,
    supporting Federer 4.1.7, p. 359,
    by 4.1.6, p. 354.
    No construction or continuity conclusion
    is part of this independent specification. *)
Definition is_smooth_form_pullback (P:Hom E F):Prop:=
  forall phi x,U x->has_differential_form_pullback NX NY U V f (ev phi) x (fv (P phi) x).

(** Source for [smooth_form_pullback_values]:
    the actual smooth pullback is
    A^m Df(x) applied to phi(f(x)),
    supporting Federer 4.1.7, p. 359.
    L is any actual original differential;
    uniqueness identifies its value. *)
Lemma smooth_form_pullback_values (P:Hom E F):
  is_smooth_form_pullback P->forall phi x (L:Hom X Y),U x->
    has_norm_differential NX NY U f x L->
    fv (P phi) x=A_m_dual (hom_as_linear L) (ev phi (f x)).
Proof.
move=>hP phi x L hx hL.
have [_ [M [hM hValue]]]:=hP phi x hx.
by rewrite (norm_differential_unique hNX hNY hM hL) in hValue.
Qed.

(** Source for [smooth_form_pullback_unique]:
    the independent actual smooth pullback
    law determines a unique linear operator,
    supporting Federer 4.1.7, p. 359.
    The original smooth-space extensionality
    and partial pullback uniqueness suffice. *)
Lemma smooth_form_pullback_unique (NF:A_m X R^o m->R) (hNF:is_real_norm NF)
    (hF:is_smooth_function_space hNX hNF U fv) (P Q:Hom E F):
  is_smooth_form_pullback P->is_smooth_form_pullback Q->P=Q.
Proof.
move=>hP hQ;apply:hom_ext=>phi;apply:(smooth_function_extensional hF)=>x hx.
exact:(differential_form_pullback_unique hNX hNY (hP phi x hx) (hQ phi x hx)).
Qed.
End SmoothFormPullbackUP.
