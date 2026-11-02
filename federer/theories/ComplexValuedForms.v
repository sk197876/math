(** Federer (1969), 1.6.6, pp. 26-27: real alternating forms with complex
    coefficients form a complex vector space. We first specify real
    alternation on the actual space of complex-valued functions. The module
    structure is pointwise and is identified with A_m over R. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import ScalarRestriction AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ComplexValued.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variable U : lmodType R.
Variable W : lmodType C.
Variable m : nat.
Local Notation WR := (restricted_space embed W).
Local Notation F := (GRing.Lmodule.clone C (m.-tuple U -> W) _).

(** Source for [complex_valued_form_pred]: Federer 1.6.6, p. 26,
    the ambient real alternating forms with complex values. The defining
    predicate, generalised to vector-valued coefficients and any field
    embedding; complex multilinearity is an additional condition. *)
Definition complex_valued_form_pred (f : F) := @form_pred R U WR m f.

(** Source for [complex_valued_form]: Federer 1.6.6, pp. 26-27,
    the complex vector space of real alternating forms. Its carrier is
    the subtype of functions satisfying the stated real form laws. *)
Record complex_valued_form := ComplexValuedForm {
  complex_form_fun : m.-tuple U -> W;
  complex_form_proof : complex_valued_form_pred complex_form_fun
}.
Coercion complex_form_fun : complex_valued_form >-> Funclass.

(** Source for [complex_valued_form_rect]: Federer 1.6.6, p. 26,
    supporting subtype interface for the space of forms. *)
Definition complex_valued_form_rect (P : complex_valued_form -> Type)
    (h : forall f hf, P (@ComplexValuedForm f hf)) (z : complex_valued_form) : P z :=
  match z as z' return P z' with @ComplexValuedForm f hf => h f hf end.
HB.instance Definition _ := [isSub for complex_form_fun by complex_valued_form_rect].
HB.instance Definition _ := [Choice of complex_valued_form by <:].

(** Source for [complex_valued_forms_closed]: Federer 1.6.6,
    pp. 26-27, complex vector space of real alternating forms.
    Closure under the pointwise complex module operations. *)
Lemma complex_valued_forms_closed : GRing.submod_closed complex_valued_form_pred.
Proof.
split.
- apply/asboolP; split; last by move=> t _.
  by move=> s t h a x y; rewrite /= scaler0 add0r.
- move=> c f g /asboolP [hf af] /asboolP [hg ag]; apply/asboolP; split.
  + move=> s t h a x y.
    change (c *: f (context_tuple s t h (a *: x + y)) +
      g (context_tuple s t h (a *: x + y)) =
      embed a *: (c *: f (context_tuple s t h x) + g (context_tuple s t h x)) +
      (c *: f (context_tuple s t h y) + g (context_tuple s t h y))).
    rewrite (hf s t h) (hg s t h).
    change (c *: (embed a *: f (context_tuple s t h x) + f (context_tuple s t h y)) +
      (embed a *: g (context_tuple s t h x) + g (context_tuple s t h y)) =
      embed a *: (c *: f (context_tuple s t h x) + g (context_tuple s t h x)) +
      (c *: f (context_tuple s t h y) + g (context_tuple s t h y))).
    by rewrite !scalerDr !scalerA addrACA [c * embed a]mulrC.
  + move=> t ht; change (c *: f t + g t = 0).
    by rewrite af // ag // scaler0 add0r.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  C F complex_valued_form_pred complex_valued_form complex_valued_forms_closed.

(** Source for [complex_valued_form_ext]: Federer 1.6.6, p. 26,
    supporting extensionality for the specified function space. *)
Lemma complex_valued_form_ext (a b : complex_valued_form) : a =1 b -> a = b.
Proof. move=> h; apply: val_inj; exact: funext h. Qed.

(** Source for [complex_valued_form_addE]: Federer 1.6.6,
    p. 26, complex vector space of forms. Addition is pointwise. *)
Lemma complex_valued_form_addE (a b : complex_valued_form) t :
  (a + b) t = a t + b t.
Proof. by []. Qed.

(** Source for [complex_valued_form_scaleE]: Federer 1.6.6,
    p. 26, complex vector space of forms. Scalar multiplication is pointwise. *)
Lemma complex_valued_form_scaleE c (a : complex_valued_form) t :
  (c *: a) t = c *: a t.
Proof. by []. Qed.

(** Source for [complex_valued_as_real]: Federer 1.6.6, p. 26,
    the ambient space A^m(V,W). Identification with the real form space. *)
Definition complex_valued_as_real (a : complex_valued_form) : A_m U WR m :=
  @AlternatingForm R U WR m a (complex_form_proof a).

(** Source for [real_as_complex_valued]: Federer 1.6.6, p. 26,
    the complex vector space on the ambient real forms. Identification
    in the other direction, retaining the actual function values. *)
Definition real_as_complex_valued (a : A_m U WR m) : complex_valued_form :=
  @ComplexValuedForm a (form_proof a).

(** Source for [complex_valued_realK]: Federer 1.6.6, p. 26,
    supporting verification that the two carriers represent the same forms. *)
Lemma complex_valued_realK : cancel complex_valued_as_real real_as_complex_valued.
Proof. by move=> a; apply: complex_valued_form_ext. Qed.

(** Source for [real_complex_valuedK]: Federer 1.6.6, p. 26,
    supporting verification that the two carriers represent the same forms. *)
Lemma real_complex_valuedK : cancel real_as_complex_valued complex_valued_as_real.
Proof. by move=> a; apply: form_ext. Qed.
End ComplexValued.
