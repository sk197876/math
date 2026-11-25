(** Federer (1969), 3.1.18, p. 229: restrict a class-one field to
    an open neighbourhood before applying the inverse-function theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormClassHigherRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_class_one_field_open_restriction]: class one and
    its actual differential are unchanged on an open restriction,
    supporting g restricted to U in Federer 3.1.18, p. 229. *)
Lemma norm_class_one_field_open_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (A B:X->Prop) (f:X->Y) (D:X->Hom X Y) :
  (forall x, B x -> A x) ->
  (forall x, B x -> norm_domain_interior NX B x) ->
  is_norm_class_one_field NX NY A f D ->
  is_norm_class_one_field NX NY B f D.
Proof.
move=>hBA hopen hD; constructor.
- exact: norm_class_zero_open_restriction hBA hopen (norm_class_one_zero hD).
- move=>x hx; exact: norm_differential_restrict hBA (hopen x hx)
    (norm_class_one_differential hD (hBA x hx)).
- move=>x hx e he.
  have [r [hr hb]] := norm_class_one_continuity hD (hBA x hx) he.
  exists r; split=>// z hz hs v; exact: hb z (hBA _ hz) hs v.
Qed.
