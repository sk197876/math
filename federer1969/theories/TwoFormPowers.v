(** Federer (1969), 1.8.2, p. 40: the m-th exterior power of
    the Hermitian imaginary two-form has degree 2m. Powers are taken
    in the existing unital alternating algebra; the homogeneous
    interface below preserves that definition, including m=0. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom AlgebraUP Bilinear AlgebraPowers GradedAlgebra
  AlternatingForms AlternatingSum AlternatingProduct AlternatingUnit
  ScalarCoefficients AlternatingZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Powers.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation A := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation pow := (@algebra_power K A).

(** Source for [two_form_power_homogeneous]: Federer 1.8.2,
    p. 40, the m-th power of a two-form has degree m+m. *)
Lemma two_form_power_homogeneous (phi : A_m V K^o 2) m :
  homogeneous (A_star_grading V K^o) (m+m) (pow (form_include phi) m).
Proof.
elim: m => [|m ih]; first exact: coefficient_form_homogeneous.
rewrite addSn addnS.
change (homogeneous (A_star_grading V K^o) (2+(m+m))
  (alternating_wedge h2 (scalar_bilinear K) (form_include phi)
    (pow (form_include phi) m))).
apply: alternating_wedge_graded; [exact: form_include_homogeneous | exact ih].
Qed.

(** Source for [two_form_power]: Federer 1.8.2, p. 40,
    A^m as a homogeneous (m+m)-covector, including the unit in degree zero. *)
Definition two_form_power (phi : A_m V K^o 2) m : A_m V K^o (m+m) :=
  form_component (m+m) (pow (form_include phi) m).

(** Source for [two_form_power_include]: Federer 1.8.2,
    p. 40, the homogeneous power agrees with the algebra power. *)
Lemma two_form_power_include phi m :
  form_include (two_form_power phi m) = pow (form_include phi) m.
Proof. rewrite /two_form_power form_componentK; exact: two_form_power_homogeneous. Qed.

(** Source for [two_form_power_zero]: Federer 1.8.2,
    p. 40, the zeroth exterior power is the multiplicative unit. *)
Lemma two_form_power_zero phi : two_form_power phi 0 = zero_form V (1 : K^o).
Proof. by rewrite /two_form_power /= /coefficient_form form_includeK. Qed.

(** Source for [two_form_power_one]: Federer 1.8.2,
    p. 40, the first exterior power is the given two-form. *)
Lemma two_form_power_one phi : two_form_power phi 1 = phi.
Proof. by rewrite /two_form_power algebra_power1 form_includeK. Qed.

(** Source for [two_form_power_scale]: Federer 1.8.2,
    p. 40, supporting homogeneity of the normal-form power computation. *)
Lemma two_form_power_scale c phi m :
  two_form_power (c *: phi) m = c^+m *: two_form_power phi m.
Proof.
by rewrite /two_form_power linearZ algebra_power_scale linearZ.
Qed.
End Powers.
