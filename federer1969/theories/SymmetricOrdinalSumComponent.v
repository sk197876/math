(** Supporting Federer (1969), 3.4.8(5), p. 328:
    extract original Taylor coefficients from a finite dependent
    family. This connects the ordinal family to the existing
    graded-sum laws of 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum Graded GradedSums SymmetricForms SymmetricFormSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [sform_ordinal_sum_component]: supporting exact
    original Taylor truncation for Federer 3.4.8(5), p. 328.
    This is the existing finite-sum component law with an actual
    dependent ordinal family; no artificial values at later orders
    are required. *)
Lemma sform_ordinal_sum_component (K:fieldType) (X Y:lmodType K) l
    (F:forall k:'I_l,S_m X Y k) (k:'I_l):
  sform_component k (\sum_(j<l) sform_include (F j)) = F k.
Proof.
apply:(can_inj (@sform_includeK K X Y k)).
rewrite sform_componentK linear_sum.
under eq_bigr do rewrite sform_include_grade.
rewrite -big_mkcond.
rewrite (big_pred1 k);first reflexivity.
move=>j;change ((val k==val j) = (j==k)).
by rewrite -val_eqE eq_sym.
Qed.
