(** Federer (1969), 1.6.6, p. 26: the complex multilinear forms constitute a
    complex vector subspace of the real alternating forms. The predicate is
    Federer's pointwise condition; the inclusion from forms defined over C
    realises it without a dimension restriction. Source context are recorded
    in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction AlternatingForms
  ComplexValuedForms ComplexAlternatingForms ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Subspace.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variables V W : lmodType C.
Variable m : nat.
Local Notation VR := (restricted_space embed V).
Local Notation CF := (complex_valued_form embed VR W m).

(** Source for [complex_form_subspace]: Federer 1.6.6, p. 26,
    opening definition and complex subalgebra assertion. Specification
    of its homogeneous vector subspace by complex multilinearity,
    with all three closure obligations proved. *)
Definition complex_form_subspace : subspace CF.
Proof.
apply: (@Subspace C CF (fun a => @m_linear C V W m a)).
- by move=> s t h a x y; rewrite /= scaler0 add0r.
- move=> f g hf hg s t h a x y.
  change (f (context_tuple s t h (a *: x + y)) + g (context_tuple s t h (a *: x + y)) =
    a *: (f (context_tuple s t h x) + g (context_tuple s t h x)) +
    (f (context_tuple s t h y) + g (context_tuple s t h y))).
  by rewrite (hf s t h) (hg s t h) scalerDr addrACA.
- move=> c f hf s t h a x y.
  change (c *: f (context_tuple s t h (a *: x + y)) =
    a *: (c *: f (context_tuple s t h x)) + c *: f (context_tuple s t h y)).
  by rewrite (hf s t h) scalerDr !scalerA [c * a]mulrC.
Defined.

(** Source for [complex_form_inclusion]: Federer 1.6.6, p. 26,
    opening subset assertion. The inclusion of a complex alternating
    form in the complex vector space of real alternating forms. *)
Definition complex_form_inclusion (a : A_m V W m) : CF :=
  real_as_complex_valued (restrict_form embed a).

(** Source for [complex_form_inclusion_linear]: Federer 1.6.6,
    p. 26, complex subspace assertion. Its inclusion is C-linear. *)
Lemma complex_form_inclusion_linear : linear complex_form_inclusion.
Proof.
move=> c a b; apply: complex_valued_form_ext => t.
change ((c *: a + b) t = c *: a t + b t).
by rewrite form_addE form_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build C (A_m V W m) CF *:%R
  complex_form_inclusion complex_form_inclusion_linear.

(** Source for [complex_form_inclusion_injective]: Federer
    1.6.6, p. 26, opening subset assertion. Values determine the
    original complex alternating form uniquely. *)
Lemma complex_form_inclusion_injective : injective complex_form_inclusion.
Proof.
move=> a b h; apply: form_ext => t.
have ht := congr1 (fun f : CF => f t) h.
exact ht.
Qed.

(** Source for [complex_form_subspace_image]: Federer 1.6.6,
    p. 26, opening definition. The stated complex subspace is exactly
    the image of the independently defined alternating forms over C. *)
Theorem complex_form_subspace_image a : complex_form_subspace a <->
  exists b : A_m V W m, complex_form_inclusion b = a.
Proof.
split.
- move=> ha.
  have hb : complex_multilinear_form (complex_valued_as_real a) := ha.
  exists (complex_form hb); apply: complex_valued_form_ext => t; by [].
- move=> [b <-].
  exact: (@form_multilinear C V W m b).
Qed.
End Subspace.
