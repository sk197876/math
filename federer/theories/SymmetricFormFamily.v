(** Federer (1969), 1.10.5, p. 47, the shuffle argument for product norms;
    supporting iterated form of the binary formula in 1.10.2, p. 45. The
    unsigned formula uses ordered coefficient multiplication.
    Right-associated products let the proof work for any bilinear
    multiplication; in an associative algebra this is the unparenthesized
    product in the sources. Nonempty products do not require a coefficient
    unit. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP Bilinear AlgebraUP Graded GradedComponents
  Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormSum SymmetricFormProduct SymmetricFormShuffle NonemptyProduct
  MultipleShuffles PermutationArguments ShuffleComposition SingleBlockShuffle
  MultipleShuffleBijection MultipleShuffleSums OneDegreeShuffles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Families.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [symmetric_form_family]: Federer 1.10.5, p. 47, supporting
    iterated shuffle calculation from 1.10.2, p. 45. In words: An ordered
    degree list specifies the symmetric-form space for each factor. *)
Definition symmetric_form_family degrees := forall i : 'I_(size degrees), S_m V W (nth 0%N degrees i).

(** Source for [symmetric_form_family_list]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Include the ordered factors in the full symmetric-form algebra. *)
Definition symmetric_form_family_list degrees (alpha : symmetric_form_family degrees) : seq (S_star V W) :=
  [seq sform_include (alpha i) | i <- enum 'I_(size degrees)].

(** Source for [symmetric_form_family_head]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Extract the first symmetric form with its stated degree. *)
Definition symmetric_form_family_head p ds (alpha : symmetric_form_family (p::ds)) : S_m V W p := alpha ord0.

(** Source for [symmetric_form_family_tail]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Restrict the family to all factors after the first. *)
Definition symmetric_form_family_tail p ds (alpha : symmetric_form_family (p::ds)) : symmetric_form_family ds :=
  fun i => alpha (lift ord0 i).

(** Source for [symmetric_form_family_list_size]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The list of included forms has exactly as many entries as the degree
    list. *)
Lemma symmetric_form_family_list_size degrees (alpha : symmetric_form_family degrees) :
  size (symmetric_form_family_list alpha) = size degrees.
Proof. by rewrite /symmetric_form_family_list size_map size_enum_ord. Qed.

(** Source for [symmetric_form_family_list_cons]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Including a family separates into its head and included tail. *)
Lemma symmetric_form_family_list_cons p ds (alpha : symmetric_form_family (p::ds)) :
  symmetric_form_family_list alpha = sform_include (symmetric_form_family_head alpha) :: symmetric_form_family_list (symmetric_form_family_tail alpha).
Proof.
rewrite /symmetric_form_family_list enum_ordSl map_cons.
congr (_ :: _); exact (esym (map_comp (fun i => sform_include (alpha i)) (lift ord0) (enum 'I_(size ds)))).
Qed.

(** Source for [symmetric_form_family_list_nil]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The empty family gives an empty list. *)
Lemma symmetric_form_family_list_nil (alpha : symmetric_form_family [::]) : symmetric_form_family_list alpha = [::].
Proof. by rewrite /symmetric_form_family_list enum_ord0. Qed.

(** Source for [symmetric_form_family_list_nonempty]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words: A
    nonempty family gives a nonempty list of factors. *)
Lemma symmetric_form_family_list_nonempty degrees (alpha : symmetric_form_family degrees) :
  degrees != [::] -> symmetric_form_family_list alpha != [::].
Proof.
move=> hd; apply/eqP=> he; have hs := congr1 size he.
by move: hd; rewrite -size_eq0 -(symmetric_form_family_list_size alpha) hs.
Qed.
End Families.
Arguments symmetric_form_family {K} V W degrees.

Section Products.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.

(** Source for [symmetric_family_product]: Federer 1.10.5, p. 47, supporting
    iterated shuffle calculation from 1.10.2, p. 45. In words: Multiply the
    included forms in order; zero is only the unused empty-family default. *)
Definition symmetric_family_product degrees (alpha : symmetric_form_family V W degrees) : S_star V W :=
  nonempty_product (symmetric_forms_product hmu) 0 (symmetric_form_family_list alpha).

(** Source for [symmetric_family_product_single]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words: A
    product with one factor is that factor. *)
Lemma symmetric_family_product_single p (alpha : symmetric_form_family V W [::p]) :
  symmetric_family_product alpha = sform_include (symmetric_form_family_head alpha).
Proof. by rewrite /symmetric_family_product symmetric_form_family_list_cons symmetric_form_family_list_nil. Qed.

(** Source for [symmetric_family_product_cons]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words: A
    nonempty tail gives the recursive binary product decomposition. *)
Lemma symmetric_family_product_cons p ds (alpha : symmetric_form_family V W (p::ds)) : ds != [::] ->
  symmetric_family_product alpha = symmetric_forms_product hmu
    (sform_include (symmetric_form_family_head alpha)) (symmetric_family_product (symmetric_form_family_tail alpha)).
Proof.
move=> hd; rewrite /symmetric_family_product symmetric_form_family_list_cons nonempty_product_cons //.
exact: symmetric_form_family_list_nonempty hd.
Qed.

(** Source for [symmetric_family_product_homogeneous]: Federer 1.10.5, p.
    47, supporting iterated shuffle calculation from 1.10.2, p. 45. In
    words: The total degree of the product is the sum of the factor degrees. *)
Lemma symmetric_family_product_homogeneous degrees (alpha : symmetric_form_family V W degrees) :
  degrees != [::] -> homogeneous (S_star_grading V W) (sumn degrees) (symmetric_family_product alpha).
Proof.
elim: degrees alpha => [|p ds ih] alpha //.
case: ds ih alpha => [|q ds] ih alpha hd.
- rewrite symmetric_family_product_single /= addn0; exact: sform_include_homogeneous.
- rewrite symmetric_family_product_cons //.
  apply: symmetric_forms_product_graded; first exact: sform_include_homogeneous.
  exact: ih.
Qed.

(** Source for [symmetric_iterated_form]: Federer 1.10.5, p. 47, supporting
    iterated shuffle calculation from 1.10.2, p. 45. In words: Restrict the
    graded product to its total-degree symmetric-form space. *)
Definition symmetric_iterated_form degrees (alpha : symmetric_form_family V W degrees) : S_m V W (sumn degrees) :=
  sform_component (sumn degrees) (symmetric_family_product alpha).

(** Source for [symmetric_iterated_formE]: Federer 1.10.5, p. 47, supporting
    iterated shuffle calculation from 1.10.2, p. 45. In words: The
    restricted form evaluates as the full product on the corresponding
    symmetric word. *)
Lemma symmetric_iterated_formE degrees (alpha : symmetric_form_family V W degrees) (t : (sumn degrees).-tuple V) :
  symmetric_iterated_form alpha t = symmetric_family_product alpha (symmetric_word t).
Proof. exact: sform_componentE. Qed.

(** Source for [symmetric_iterated_form_include]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Including the restricted form recovers the full homogeneous product. *)
Lemma symmetric_iterated_form_include degrees (alpha : symmetric_form_family V W degrees) : degrees != [::] ->
  sform_include (symmetric_iterated_form alpha) = symmetric_family_product alpha.
Proof. move=> hd; rewrite /symmetric_iterated_form sform_componentK; exact: symmetric_family_product_homogeneous hd. Qed.
End Products.
