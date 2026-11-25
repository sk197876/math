(** Federer (1969), 4.1.6, pp. 354–355: the
    original pullback of a one-form is composition
    of its ordinary linear map with Df. This
    supports the coordinate-generator proof of
    commutation with exterior differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Alternating OneFormLinear OneFormIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [original_pullback_one_form]: the
    original A^1 Df identification in the defining
    pullback formula, Federer 4.1.6,
    p. 354, for arbitrary vector coefficients. *)
Lemma original_pullback_one_form (K:fieldType) (X Y W:lmodType K)
    (f:Hom X Y) (a:Hom Y W):
  A_m_dual (hom_as_linear f) (one_form a)=one_form (hom_comp a f).
Proof.
apply:(can_inj (@one_homK K X W)); apply:hom_ext=>v.
rewrite one_formK hom_compE.
change (A_m_dual (hom_as_linear f) (one_form a) [tuple v]=a (f v)).
rewrite A_m_dualE.
have hTuple:[tuple of map (hom_as_linear f) [tuple v]]=[tuple f v].
  by apply:eq_from_tnth=>i; rewrite (ord1 i) tnth_map.
change (one_form a [tuple of map (hom_as_linear f) [tuple v]]=a (f v)).
by rewrite hTuple one_formE.
Qed.
