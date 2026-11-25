(** Federer (1969), 1.6.6, p. 26, opening definition: complex alternating
    forms are the real alternating forms which are complex linear in each
    argument. No dimension hypothesis is imposed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import ScalarRestriction AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Forms.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variables V W : lmodType C.
Variable m : nat.
Local Notation VR := (restricted_space embed V).
Local Notation WR := (restricted_space embed W).

(** Source for [complex_multilinear_form]: Federer 1.6.6, p. 26,
    opening definition. The predicate of complex linearity in each
    argument, on an already real alternating form. This formulation
    generalises the real-to-complex embedding to any field embedding. *)
Definition complex_multilinear_form (a : A_m VR WR m) : Prop :=
  @m_linear C V W m a.

(** Source for [restrict_formP]: Federer 1.6.6, p. 26, opening
    subset assertion. A complex alternating form is real alternating. *)
Lemma restrict_formP (a : A_m V W m) :
  @form_pred R VR WR m a.
Proof.
apply/asboolP; split.
- move=> s t h c x y.
  have hc z : @context_tuple R VR m s t h z = @context_tuple C V m s t h z.
    by apply: val_inj.
  rewrite !hc.
  exact: (@form_multilinear C V W m a s t h (embed c) x y).
- exact: (@form_alternating C V W m a).
Qed.

(** Source for [restrict_form]: Federer 1.6.6, p. 26, opening
    subset assertion. The inclusion of complex alternating forms into
    the real alternating forms, leaving their values unchanged. *)
Definition restrict_form (a : A_m V W m) : A_m VR WR m :=
  @AlternatingForm R VR WR m a (restrict_formP a).

(** Source for [restrict_form_complex]: Federer 1.6.6, p. 26,
    opening definition. The inclusion satisfies complex multilinearity. *)
Lemma restrict_form_complex a : complex_multilinear_form (restrict_form a).
Proof. exact: (@form_multilinear C V W m a). Qed.

(** Source for [complex_formP]: Federer 1.6.6, p. 26, opening
    definition. Complex multilinearity and real alternation suffice for
    a complex alternating form. *)
Lemma complex_formP (a : A_m VR WR m) (ha : complex_multilinear_form a) :
  @form_pred C V W m a.
Proof. by apply/asboolP; split=> //; exact: (@form_alternating R VR WR m a). Qed.

(** Source for [complex_form]: Federer 1.6.6, p. 26, opening
    definition. Recognition of a real alternating form as complex. *)
Definition complex_form (a : A_m VR WR m) (ha : complex_multilinear_form a) : A_m V W m :=
  @AlternatingForm C V W m a (@complex_formP a ha).

(** Source for [complex_form_restrict]: Federer 1.6.6, p. 26,
    opening subset definition. The recognition and inclusion cancel. *)
Lemma complex_form_restrict a :
  complex_form (restrict_form_complex a) = a.
Proof. by apply: form_ext. Qed.

(** Source for [restrict_complex_form]: Federer 1.6.6, p. 26,
    opening subset definition. Every qualifying real form is in the
    image of the complex-form inclusion. *)
Lemma restrict_complex_form a ha : restrict_form (@complex_form a ha) = a.
Proof. by apply: form_ext. Qed.

(** Source for [restrict_form_injective]: Federer 1.6.6, p. 26,
    opening subset assertion. The inclusion is injective. *)
Lemma restrict_form_injective : injective restrict_form.
Proof.
move=> a b h; apply: form_ext => t.
have ht := congr1 (fun c : A_m VR WR m => c t) h.
exact ht.
Qed.

(** Source for [complex_form_image]: Federer 1.6.6, p. 26,
    opening definition. Exact characterisation of the specified subset
    by the independently defined alternating forms over C. *)
Lemma complex_form_image a : complex_multilinear_form a <->
  exists b : A_m V W m, restrict_form b = a.
Proof.
split.
- by move=> ha; exists (@complex_form a ha); exact: restrict_complex_form.
- by move=> [b <-]; exact: restrict_form_complex.
Qed.
End Forms.
