(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section LinearRules.
Variable K : fieldType.
Variables U Z : lmodType K.
Variable f : U -> Z.
Hypothesis hf : linear f.

(** Source for [lin0]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma lin0 : f 0 = 0.
Proof. by have := GRing.scalable_linear hf 0 (0 : U); rewrite /= !scale0r. Qed.
(** Source for [linD]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linD x y : f (x + y) = f x + f y.
Proof. by have := hf 1 x y; rewrite !scale1r. Qed.
(** Source for [linZ]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linZ a x : f (a *: x) = a *: f x.
Proof. exact (GRing.scalable_linear hf a x). Qed.
(** Source for [linB]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linB x y : f (x - y) = f x - f y.
Proof. exact (GRing.zmod_morphism_linear hf x y). Qed.
End LinearRules.

Section BilinearRules.
Variable K : fieldType.
Variables U V Z : lmodType K.
Variable b : U -> V -> Z.
Hypothesis hb : bilinear b.

(** Source for [bil0l]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bil0l y : b 0 y = 0.
Proof. exact: lin0 (proj1 hb y). Qed.
(** Source for [bil0r]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bil0r x : b x 0 = 0.
Proof. exact: lin0 (proj2 hb x). Qed.
(** Source for [bilDl]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilDl x x' y : b (x + x') y = b x y + b x' y.
Proof. exact (linD (proj1 hb y) x x'). Qed.
(** Source for [bilDr]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilDr x y y' : b x (y + y') = b x y + b x y'.
Proof. exact (linD (proj2 hb x) y y'). Qed.
(** Source for [bilZl]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilZl a x y : b (a *: x) y = a *: b x y.
Proof. exact (linZ (proj1 hb y) a x). Qed.
(** Source for [bilZr]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilZr a x y : b x (a *: y) = a *: b x y.
Proof. exact (linZ (proj2 hb x) a y). Qed.
(** Source for [bilBl]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilBl x x' y : b (x - x') y = b x y - b x' y.
Proof. exact (linB (proj1 hb y) x x'). Qed.
(** Source for [bilBr]: Federer (1969), 1.1.1, p. 8, opening definition. In
    words: An n-linear function is linear in each argument when all other
    arguments are fixed. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma bilBr x y y' : b x (y - y') = b x y - b x y'.
Proof. exact (linB (proj2 hb x) y y'). Qed.
End BilinearRules.

Section FreeInduction.
Variable K : fieldType.
Variable A : choiceType.

(** Source for [free_induction]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_induction (P : free_vector K A -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hd : forall a, P (delta K a)) : forall f, P f.
Proof.
move=> f; rewrite (free_expansion f).
apply: big_ind => // a _; exact: hZ (hd a).
Qed.
End FreeInduction.

Section BilinearExtension.
Variable K : fieldType.
Variables A B : choiceType.
Variable Z : lmodType K.
Variable h : A -> B -> Z.
Local Notation F := (free_vector K A).
Local Notation G := (free_vector K B).

(** Source for [free_bilinear]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Definition or construction used to
    formalise this passage. *)
Definition free_bilinear (f : F) (g : G) :=
  free_extend (fun a => free_extend (h a) g) f.

(** Source for [free_bilinear0l]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinear0l g : free_bilinear 0 g = 0.
Proof. exact: linear0. Qed.
(** Source for [free_bilinearDl]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinearDl f f' g :
  free_bilinear (f + f') g = free_bilinear f g + free_bilinear f' g.
Proof. exact: linearD. Qed.
(** Source for [free_bilinearZl]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinearZl a f g : free_bilinear (a *: f) g = a *: free_bilinear f g.
Proof. exact: linearZ. Qed.
(** Source for [free_bilinear_delta_l]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinear_delta_l a g : free_bilinear (delta K a) g = free_extend (h a) g.
Proof. exact: free_extend_delta. Qed.

(** Source for [free_bilinear_linear_r]: Federer (1969), 1.1.1, p. 8,
    opening definition. In words: An n-linear function is linear in each
    argument when all other arguments are fixed. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_bilinear_linear_r f : linear (free_bilinear f).
Proof.
elim/free_induction: f => [|f f' hf hf'|a f hf|x] c g g'.
- by rewrite !free_bilinear0l scaler0 add0r.
- by rewrite !free_bilinearDl hf hf' scalerDr addrACA.
- by rewrite !free_bilinearZl hf scalerDr !scalerA (mulrC a c).
- by rewrite !free_bilinear_delta_l linearP.
Qed.

(** Source for [free_bilinear_bilinear]: Federer (1969), 1.1.1, p. 8,
    opening definition. In words: An n-linear function is linear in each
    argument when all other arguments are fixed. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_bilinear_bilinear : bilinear free_bilinear.
Proof.
split; last exact: free_bilinear_linear_r.
by move=> g a f f'; rewrite free_bilinearDl free_bilinearZl.
Qed.

(** Source for [free_bilinearE]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinearE a b : free_bilinear (delta K a) (delta K b) = h a b.
Proof. by rewrite free_bilinear_delta_l free_extend_delta. Qed.
End BilinearExtension.

Section BilinearExtensionality.
Variable K : fieldType.
Variables A B : choiceType.
Variable Z : lmodType K.
Variables f g : free_vector K A -> free_vector K B -> Z.
Hypotheses (hf : bilinear f) (hg : bilinear g).

(** Source for [free_bilinear_ext]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_bilinear_ext :
  (forall a b, f (delta K a) (delta K b) = g (delta K a) (delta K b)) ->
  forall x y, f x y = g x y.
Proof.
move=> e; apply: free_induction => [y|x x' hx hx' y|a x hx y|a].
- by rewrite (bil0l hf) (bil0l hg).
- by rewrite (bilDl hf) (bilDl hg) hx hx'.
- by rewrite (bilZl hf) (bilZl hg) hx.
apply: free_induction => [|y y' hy hy'|b y hy|b].
- by rewrite (bil0r hf) (bil0r hg).
- by rewrite (bilDr hf) (bilDr hg) hy hy'.
- by rewrite (bilZr hf) (bilZr hg) hy.
exact: e.
Qed.
End BilinearExtensionality.
