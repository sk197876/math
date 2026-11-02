(** Federer (1969), 1.10.5, p. 48: supporting diagonal character of a
    secondary maximizing scalar form tuple. The local proof extracts any two
    entries by a permutation, applies the proved two-entry result, and then
    identifies the list as a repeated vector. Source context and context:
    HilbertWordPair.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm SymmetricForms SymmetricFormWords
  HilbertWordPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [constant_member_list]: Federer 1.10.5,
    p. 48, supporting identification of a tuple with equal
    entries as a repeated vector of the same length. *)
Lemma constant_member_list (T : eqType) (x:T) (s:seq T) :
  (forall y, y\in s -> y=x) -> s=nseq (size s) x.
Proof.
elim: s=> [|y s ih] hh //=.
have hy : y=x := hh y (mem_head _ _).
rewrite hy; congr (_::_); apply: ih=> z hz; apply: hh; by rewrite in_cons hz orbT.
Qed.

(** Source for [hilbert_secondary_word_diagonal]: Federer
    1.10.5, p. 48, supporting conclusion that a nonempty
    secondary maximizing word with unit entries is diagonal. No finite
    dimensional hypothesis is used here; compactness supplies the word
    separately in the finite-dimensional application. *)
Theorem hilbert_secondary_word_diagonal (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m (f : S_m V R^o m) M
    (hmax : forall r, size r=m ->
      (forall v, v\in r -> inner_norm hB v<=1) -> `|sform_words f r|<=M)
    s (hs : size s=m) (hne : s!=[::])
    (hu : forall v, v\in s -> inner_norm hB v= 1)
    (he : `|sform_words f s|=M)
    (hsecondary : forall r, size r=m ->
      (forall v, v\in r -> inner_norm hB v<=1) -> `|sform_words f r|=M ->
      inner_norm hB (\sum_(v<-r) v)<=inner_norm hB (\sum_(v<-s) v)) :
  exists x, inner_norm hB x= 1 /\ s=nseq m x.
Proof.
case: s hs hne hu he hsecondary=> [|x s] hs // hne hu he hsecondary.
have hall : forall y, y\in s -> y=x.
  move=> y hy.
  case/splitPr: hy hs hu he hsecondary=> p q hs hu he hsecondary.
  have hp : perm_eq (x::p++y::q) (x::y::p++q).
    rewrite perm_cons.
    change (perm_eq (p++[::y]++q) ([::y]++p++q)).
    by rewrite perm_catCA.
  have hsz : size (x::y::p++q)=m by rewrite -(perm_size hp).
  have huz : forall v, v\in x::y::p++q -> inner_norm hB v= 1.
    move=> v hv; apply: hu; by rewrite (perm_mem hp).
  have hez : `|sform_words f (x::y::p++q)|=M.
    rewrite -(@sform_words_symmetric R V R^o m f _ _ hp); exact he.
  have hsum : (\sum_(v<-x::p++y::q) v)=(\sum_(v<-x::y::p++q) v).
    exact: perm_big hp.
  have hszmax : forall r, size r=m ->
      (forall v, v\in r -> inner_norm hB v<=1) -> `|sform_words f r|=M ->
      inner_norm hB (\sum_(v<-r) v)<=inner_norm hB (\sum_(v<-x::y::p++q) v).
    move=> r hr hunit hf; rewrite -hsum; exact: hsecondary hr hunit hf.
  exact: esym (@hilbert_word_extremal_front_equal R V B hB m f M hmax
    x y (p++q) hsz huz hez hszmax).
exists x; split; first exact: hu x (mem_head _ _).
rewrite -hs; apply: constant_member_list=> y.
rewrite in_cons=> /orP[/eqP ->|hy]; first by [].
exact: hall hy.
Qed.
