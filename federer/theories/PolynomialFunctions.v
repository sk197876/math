(** Federer (1969), 1.10.4, p. 46: polynomial functions as actual maps with
    a finite symmetric-form representation. The predicate specifies
    representation, and the proved graded-sum laws supply the structure. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Graded GradedSums Hom HomogeneousHom BoundedHom
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricFormSum HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  SymmetricPolynomialInjectivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Polynomials.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation F := (GRing.Lmodule.clone K (V -> W) _).
Local Notation A := (S_star V W).

(** Source for [is_polynomial_function]: Federer 1.10.4,
    p. 46, definition by a finite list of homogeneous coefficient
    forms. The equivalent graded-sum representation records precisely
    such a finite list. *)
Definition is_polynomial_function (P : V -> W) : Prop :=
  exists f : A, P =1 symmetric_polynomial_value f.

(** Source for [polynomial_function_pred]: Federer 1.10.4,
    p. 46, supporting boolean form of the representation predicate. *)
Definition polynomial_function_pred (P : F) := `[< is_polynomial_function P >].

(** Source for [PolynomialFunction]: Federer 1.10.4, p. 46,
    the vector space of polynomial maps from V to W. Its elements
    are actual functions with a proof of the stated representation law. *)
Record PolynomialFunction := PolynomialMap {
  polynomial_function : V -> W;
  polynomial_function_proof : polynomial_function_pred polynomial_function
}.
Coercion polynomial_function : PolynomialFunction >-> Funclass.

(** Source for [polynomial_function_rect]: Federer 1.10.4,
    p. 46, supporting eliminator for the subtype of actual functions. *)
Definition polynomial_function_rect (P : PolynomialFunction -> Type)
    (h : forall f hf, P (@PolynomialMap f hf)) (z : PolynomialFunction) : P z :=
  match z as z' return P z' with @PolynomialMap f hf => h f hf end.
HB.instance Definition _ := [isSub for polynomial_function by polynomial_function_rect].
HB.instance Definition _ := [Choice of PolynomialFunction by <:].

(** Source for [polynomial_function_closed]: Federer 1.10.4,
    p. 46, polynomial functions form a vector space under pointwise
    addition and scalar multiplication. *)
Lemma polynomial_function_closed : GRing.submod_closed polynomial_function_pred.
Proof.
split.
- apply/asboolP; exists 0=> x; by rewrite (linear0 (@symmetric_polynomial_value K V W)).
- move=> a P Q /asboolP [f hf] /asboolP [g hg]; apply/asboolP.
  exists (a *: f+g)=> x.
  change (a *: P x+Q x = symmetric_polynomial_value (a *: f+g) x).
  by rewrite linearP /= hf hg.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build K F
  polynomial_function_pred PolynomialFunction polynomial_function_closed.

(** Source for [polynomial_function_ext]: Federer 1.10.4,
    p. 46, equality of polynomial functions is equality of their values. *)
Lemma polynomial_function_ext (P Q : PolynomialFunction) : P =1 Q -> P=Q.
Proof. move=> h; apply: val_inj; exact: funext h. Qed.

(** Source for [polynomial_from_forms]: Federer 1.10.4,
    p. 46, the map in the asserted linear isomorphism. The finite
    graded-form sum is sent to its polynomial evaluation function. *)
Definition polynomial_from_forms (f : A) : PolynomialFunction :=
  @PolynomialMap (symmetric_polynomial_value f)
    (introT (asboolP _) (ex_intro _ f (fun x => erefl))).

(** Source for [polynomial_from_formsE]: Federer 1.10.4,
    p. 46, the associated function evaluates by the stated finite sum. *)
Lemma polynomial_from_formsE f x : polynomial_from_forms f x = symmetric_polynomial_value f x.
Proof. by []. Qed.

(** Source for [polynomial_from_forms_linear]: Federer 1.10.4,
    p. 46, linearity of the form-to-polynomial identification. *)
Lemma polynomial_from_forms_linear : linear polynomial_from_forms.
Proof.
move=> a f g; apply: polynomial_function_ext=> x.
change (symmetric_polynomial_value (a *: f+g) x =
  a *: symmetric_polynomial_value f x + symmetric_polynomial_value g x).
by rewrite linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K A PolynomialFunction *:%R
  polynomial_from_forms polynomial_from_forms_linear.

(** Source for [polynomial_form_representation]: Federer 1.10.4,
    p. 46, every polynomial map has a finite homogeneous representation. *)
Lemma polynomial_form_representation (P : PolynomialFunction) :
  exists f : A, polynomial_from_forms f == P.
Proof.
have [f hf] := elimT (asboolP _) (polynomial_function_proof P).
exists f; apply/eqP; apply: polynomial_function_ext=> x; exact: esym (hf x).
Qed.

(** Source for [polynomial_to_forms]: Federer 1.10.4,
    p. 46, inverse of the polynomial identification, obtained from
    existence of a representation. Uniqueness is proved in characteristic
    zero rather than postulated in this choice construction. *)
Definition polynomial_to_forms (P : PolynomialFunction) : A :=
  xchoose (polynomial_form_representation P).

(** Source for [polynomial_to_formsK]: Federer 1.10.4,
    p. 46, the chosen representation gives back the original function. *)
Lemma polynomial_to_formsK : cancel polynomial_to_forms polynomial_from_forms.
Proof. move=> P; apply/eqP; exact: xchooseP (polynomial_form_representation P). Qed.

(** Source for [polynomial_from_formsK]: Federer 1.10.4,
    p. 46, uniqueness of the coefficient forms proves the other inverse law. *)
Lemma polynomial_from_formsK (h0 : [pchar K] =i pred0) :
  cancel polynomial_from_forms polynomial_to_forms.
Proof.
move=> f; apply: (@symmetric_polynomial_injective K h0 V W).
have h := congr1 polynomial_function (polynomial_to_formsK (polynomial_from_forms f)).
exact: h.
Qed.

(** Source for [polynomial_to_forms_linear]: Federer 1.10.4,
    p. 46, the inverse representation map is also linear. *)
Lemma polynomial_to_forms_linear (h0 : [pchar K] =i pred0) : linear polynomial_to_forms.
Proof.
move=> a P Q; apply: (can_inj (polynomial_from_formsK h0)).
rewrite linearP polynomial_to_formsK.
change (a *: P+Q = a *: polynomial_from_forms (polynomial_to_forms P) +
  polynomial_from_forms (polynomial_to_forms Q)).
by rewrite !polynomial_to_formsK.
Qed.
End Polynomials.

Arguments PolynomialFunction {K} V W.
