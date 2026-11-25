(** Federer (1969), 4.1.8, p. 360: equal total
    degrees in the separated-test characterization. This
    supporting rule for the original covector grading of
    1.4.1, p. 17, identifies equal degree indices only. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom AlternatingForms AlternatingSum ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [form_component_equal_degree]: projecting a
    homogeneous covector to the same, equally indexed degree
    preserves it, supporting Federer 4.1.8, p. 360,
    by 1.4.1, p. 17. *)
Lemma form_component_equal_degree (K:fieldType) (V W:lmodType K) m n (e:m=n)
    (phi:A_m V W m):
  form_component n (form_include phi)=form_reindex e phi.
Proof. by case:n/e;rewrite form_includeK. Qed.
