(** Federer (1969), 4.1.6, p. 352: the actual
    induced norm on Euclidean-source, arbitrary normed
    coefficient forms. The exact multilinear norm is
    supplied by its proved opaque specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct AlternatingForms AlternatingFormNormUP AlternatingFormNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_form_norm]: the original
    induced form norm of Federer 4.1.6,
    p. 352, not the Euclidean covector norm
    or comass substituted for that norm. *)
Definition euclidean_form_norm (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) m:A_m (R_n R n) W m->R:=
  @AlternatingFormNorm.value R h2 (R_n R n) W
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) NW hNW m.

(** Source for [euclidean_form_norm_laws]: its exact
    original least multilinear bound,
    Federer 4.1.6, p. 352. *)
Lemma euclidean_form_norm_laws (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) m:
  is_alternating_form_norm (InnerNorm.inner_norm (@euclidean_inner_productP R n)) NW
    (@euclidean_form_norm R h2 n W NW hNW m).
Proof. exact:AlternatingFormNorm.laws. Qed.

(** Source for [euclidean_form_norm_real_norm]: the
    original induced function is a genuine finite norm,
    Federer 4.1.6, p. 352, for every degree
    and every normed coefficient space. *)
Lemma euclidean_form_norm_real_norm (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) m:
  is_real_norm (@euclidean_form_norm R h2 n W NW hNW m).
Proof. exact:AlternatingFormNorm.norm_laws. Qed.
