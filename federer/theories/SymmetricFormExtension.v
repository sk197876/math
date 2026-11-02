(** Federer (1969), 1.10.1, p. 44: the linear extension of a symmetric form.
    This uses only the abstract symmetric-algebra interface. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear GradedAlgebra Hom HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Extension.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).
Local Notation A := (S_m V W m).
(** Source for [sform_extension]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Extend a symmetric form to a linear map on the symmetric algebra through its abstract universal property. *)
Definition sform_extension (f : A) : {linear E -> W} :=
  symmetric_word_extension (sform_words_multilinear f) (sform_words_symmetric f).
(** Source for [sform_extensionE]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The extension sends a product of generating vectors to the form on that tuple, and to zero if its length differs. *)
Lemma sform_extensionE (f : A) s : sform_extension f (symmetric_word s) = sform_words f s.
Proof. exact: symmetric_word_extensionE. Qed.

(** Source for [sform_extension_degree]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The extension vanishes on all homogeneous components other than degree m. *)
Lemma sform_extension_degree (f : A) n x :
  n != m -> homogeneous G n x -> sform_extension f x = 0.
Proof.
move=> hn; move: x; apply: symmetric_component_induction => [|x y hx hy|a x hx|s hs].
- exact: linear0.
- by rewrite linearD hx hy add0r.
- rewrite linearZ; change (a *: sform_extension f x = 0).
  by rewrite hx scaler0.
- rewrite sform_extensionE; apply: sform_words_wrong; by rewrite hs.
Qed.

(** Source for [sform_extension_parameter_linear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The unique extension depends linearly on the form. *)
Lemma sform_extension_parameter_linear x : linear (fun f : A => sform_extension f x).
Proof.
move=> a f g; elim/symmetric_word_induction: x => [|x y hx hy|b x hx|s].
- by rewrite !linear0 add0r.
- rewrite (linearD (sform_extension (a *: f + g)))
    (linearD (sform_extension f)) (linearD (sform_extension g)).
  change (sform_extension (a *: f + g) x + sform_extension (a *: f + g) y =
    a *: (sform_extension f x + sform_extension f y) +
      (sform_extension g x + sform_extension g y)).
  by rewrite hx hy scalerDr addrACA.
- rewrite (linZ (linearP (sform_extension (a *: f + g))) b x)
    (linZ (linearP (sform_extension f)) b x)
    (linZ (linearP (sform_extension g)) b x).
  change (b *: sform_extension (a *: f + g) x =
    a *: (b *: sform_extension f x) + b *: sform_extension g x).
  by rewrite hx scalerDr !scalerA [b * a]mulrC.
- rewrite !sform_extensionE; exact: sform_words_linear.
Qed.

(** Source for [sform_homogeneous]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Regard the extension as a homogeneous linear map of degree m. *)
Definition sform_homogeneous (f : A) : Hom_m W G m :=
  @HomogeneousHom K E W G m (hom_of_linear (sform_extension f))
    (introT (asboolP _) (@sform_extension_degree f)).
(** Source for [sform_homogeneousE]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The packaged homogeneous map evaluates as the extension. *)
Lemma sform_homogeneousE f x : sform_homogeneous f x = sform_extension f x.
Proof. by []. Qed.
(** Source for [sform_homogeneous_linear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The passage from symmetric forms to homogeneous linear maps is linear. *)
Lemma sform_homogeneous_linear : linear sform_homogeneous.
Proof.
move=> a f g; apply: hom_m_ext => x.
rewrite hom_m_addE hom_m_scaleE !sform_homogeneousE.
exact: sform_extension_parameter_linear.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K A (Hom_m W G m)
  *:%R sform_homogeneous sform_homogeneous_linear.

End Extension.
