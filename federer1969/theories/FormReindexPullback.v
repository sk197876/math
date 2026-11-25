(** Federer (1969), 4.1.8, p. 361: equal-degree
    bookkeeping for the original signed interchange of
    separated forms. These supporting identities identify
    equal natural degrees in the existing exterior algebra. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom AlternatingForms AlternatingDual ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [form_reindex_composition]: composing the
    original equal-degree identifications changes no form,
    supporting Federer 4.1.8, p. 361. *)
Lemma form_reindex_composition (K:fieldType) (V W:lmodType K)
    a b c (e:a=b) (f:b=c) (phi:A_m V W a):
  form_reindex f (form_reindex e phi)=form_reindex (eq_trans e f) phi.
Proof. by case:b /e in f *;case:c /f. Qed.

(** Source for [original_linear_pullback_reindex]: the
    original linear pullback commutes with identification
    of equal degrees, supporting the signed product
    formula in Federer 4.1.8, p. 361. *)
Lemma original_linear_pullback_reindex (K:fieldType) (V X W:lmodType K)
    (L:Hom V X) a b (e:a=b) (phi:A_m X W a):
  A_m_dual (hom_as_linear L) (form_reindex e phi)=
    form_reindex e (A_m_dual (hom_as_linear L) phi).
Proof. by case:b /e. Qed.
