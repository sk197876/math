(** Federer (1969), 3.1.24, p. 239: expand
    each composition word on arbitrary tuples, retaining the
    operator norm rather than only the diagonal polynomial norm. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP Hom HomogeneousHom BoundedHom Graded SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormPostcompose SymmetricFormProduct SymmetricFormShuffle Shuffles AlternatingShuffle
  CompositionFormMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_form_word_tuple_successor]: supporting
    the operator bound for each term of S(p), Federer
    3.1.24, p. 239. Splitting the first inner
    differential from the remaining word and applying the
    1.10.2 shuffle formula gives the indicated binary shuffle
    expansion on an arbitrary input tuple. Empty tails are
    included, so no positive-degree restriction is hidden. *)
Lemma composition_form_word_tuple_successor (K:fieldType) (X Y:lmodType K)
    k (phi:forall i,S_m X Y i) (i:'I_k) (s:seq 'I_k)
    (t:((val i).+1+\sum_(j<-s) (val j).+1)%N.-tuple X) :
  @composition_form_word K X Y k phi (i::s) (symmetric_word t)=
    \sum_(sigma:Sh (val i).+1 (\sum_(j<-s) (val j).+1)%N)
      symmetric_product
        (symmetric_generator (phi (val i).+1 (shuffle_left_tuple t (val sigma))))
        (@composition_form_word K X Y k phi s (symmetric_word (shuffle_right_tuple t (val sigma)))).
Proof.
pose P:=(\sum_(j<-s) (val j).+1)%N.
pose w:=@composition_form_word K X Y k phi s.
pose alpha:=symmetric_form_postcompose
  (GRing.Linear.clone _ _ _ _ (@symmetric_generator K Y) _) (phi (val i).+1).
pose beta:=sform_component P w.
have hin:sform_include beta= w.
  rewrite /beta sform_componentK.
  exact (@composition_form_word_homogeneous K X Y k phi s).
have hpair:@composition_form_word K X Y k phi (i::s) (symmetric_word t)=
    sform_product (symmetric_product_bilinear Y) alpha beta t.
  change (symmetric_forms_product (symmetric_product_bilinear Y) (sform_include alpha) w
    (symmetric_word t)= sform_product (symmetric_product_bilinear Y) alpha beta t).
  by rewrite -hin -sform_product_include sform_includeE sform_extensionE sform_wordsE.
rewrite hpair sform_product_shuffle.
apply: eq_bigr=>sigma _.
rewrite /alpha symmetric_form_postcomposeE /beta sform_componentE.
reflexivity.
Qed.
