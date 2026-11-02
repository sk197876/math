(** Federer (1969), 1.10.5, p. 47, form-norm definition. Source context and
    hypotheses: SymmetricOperatorNormUP.v. The supremum includes degree-zero
    forms and zero forms, even on the zero-dimensional space. These
    supporting boundary identities prevent empty-domain or positive-degree
    assumptions entering the interface. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms SymmetricFormZero
  ExtendedSupremumUP SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Boundary.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Hypothesis hV : is_real_seminorm NV.
Variable NW : W -> R.

(** Source for [symmetric_operator_degree_zero]: Federer 1.10.5,
    p. 47, supporting degree-zero interpretation of the displayed
    supremum. A zero-form has norm equal to the norm of its sole value. *)
Theorem symmetric_operator_degree_zero (f : S_m V W 0) :
  symmetric_operator_norm hV NW f = (NW (f [tuple]))%:E.
Proof.
apply: (@symmetric_operator_norm_unique R V W NV NW 0 f);
  first exact: symmetric_operator_normP.
constructor.
- move=> r [t [ht ->]]; rewrite (tuple0 t); exact: lexx.
- move=> d hd; apply: hd; exists [tuple]; split=> //.
  by move=> i; have := ltn_ord i.
Qed.

(** Source for [symmetric_operator_constant]: Federer 1.10.5,
    p. 47, the constant zero-form corresponding to w has norm |w|. *)
Lemma symmetric_operator_constant w :
  symmetric_operator_norm hV NW (zero_sform V w) = (NW w)%:E.
Proof. by rewrite symmetric_operator_degree_zero zero_sformE. Qed.

(** Source for [symmetric_operator_zero]: Federer 1.10.5,
    p. 47, the zero symmetric form has norm zero in every degree,
    for arbitrary input dimension. *)
Theorem symmetric_operator_zero (hW : is_real_seminorm NW) m :
  symmetric_operator_norm hV NW (0 : S_m V W m) = 0%E.
Proof.
apply: (@symmetric_operator_norm_unique R V W NV NW m (0:S_m V W m));
  first exact: symmetric_operator_normP.
constructor.
- move=> r [t [ht ->]]; rewrite sform_zeroE (real_seminorm_zero hW); exact: lexx.
- move=> d hd.
  have [r [t [ht hr]]] := @symmetric_form_unit_values_nonempty R V W NV NW m hV 0.
  have hh := hd (NW ((0:S_m V W m) t)).
  rewrite sform_zeroE (real_seminorm_zero hW) in hh; apply: hh.
  exists t; split=> //; by rewrite sform_zeroE (real_seminorm_zero hW).
Qed.
End Boundary.
