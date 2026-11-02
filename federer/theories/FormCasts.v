(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.3: changing the proof of a degree
    or ordinal bound leaves the forms, values and permutation index
    unchanged. These casts connect the list-of-degrees formula of 1.4.2
    with an m-tuple of one-covectors. *)
Section FormCasts.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [form_cast]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Definition or construction used to formalise this passage. *)
Definition form_cast m n (h : m=n) (a : A_m V W m) : A_m V W n :=
  eq_rect m (A_m V W) a n h.
(** Source for [form_cast_words]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma form_cast_words m n (h : m=n) (a : A_m V W m) xs :
  form_words (form_cast h a) xs = form_words a xs.
Proof. by case: n / h. Qed.
(** Source for [form_cast_include]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma form_cast_include m n (h : m=n) (a : A_m V W m) :
  form_include (form_cast h a) = form_include a.
Proof. by case: n / h. Qed.
(** Source for [form_castE]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_castE m n (h : m=n) (a : A_m V W m) (t : n.-tuple V) :
  form_cast h a t = a (tcast (esym h) t).
Proof. by case: n / h in t *; rewrite tcast_id. Qed.
End FormCasts.
(** Source for [cast_enum]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma cast_enum m n (h : m=n) : map (cast_ord h) (enum 'I_m) = enum 'I_n.
Proof. case: n / h; under eq_map do rewrite cast_ord_id; exact: map_id. Qed.
(** Source for [index_cast_perm]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma index_cast_perm (K : fieldType) m n (h : m=n) (sigma : 'S_m) :
  FedererPermutation.index K (cast_perm h sigma) = FedererPermutation.index K sigma.
Proof. by case: n / h; rewrite cast_perm_id. Qed.
(** Source for [cast_tnth_perm]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma cast_tnth_perm (T : Type) m n (h : m=n) (t : m.-tuple T) (sigma : 'S_m) i :
  tnth (tcast h t) ((cast_perm h sigma) (cast_ord h i)) = tnth t (sigma i).
Proof. by rewrite -cast_ord_permE tcastE cast_ordK. Qed.

Section ConstantFamily.
Variable K : fieldType.
Variables V W : lmodType K.
Variables m p : nat.
(** Source for [constant_degree]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma constant_degree (i : 'I_(size (nseq m p))) : p = nth 0%N (nseq m p) i.
Proof. have hi : (i < m)%N := ltn_ord (cast_ord (size_nseq m p) i).
by rewrite nth_nseq hi.
Qed.
(** Source for [constant_form_family]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition constant_form_family (alpha : 'I_m -> A_m V W p) : form_family V W (nseq m p) :=
  fun i => form_cast (constant_degree i) (alpha (cast_ord (size_nseq m p) i)).
(** Source for [constant_family_include]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma constant_family_include (alpha : 'I_m -> A_m V W p) i :
  form_include (constant_form_family alpha i) = form_include (alpha (cast_ord (size_nseq m p) i)).
Proof. exact: form_cast_include. Qed.
(** Source for [constant_family_words]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma constant_family_words (alpha : 'I_m -> A_m V W p) i xs :
  form_words (constant_form_family alpha i) xs = form_words (alpha (cast_ord (size_nseq m p) i)) xs.
Proof. exact: form_cast_words. Qed.
(** Source for [constant_family_list]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma constant_family_list (alpha : 'I_m -> A_m V W p) :
  form_family_list (constant_form_family alpha) = [seq form_include (alpha i) | i <- enum 'I_m].
Proof.
rewrite /form_family_list.
under eq_map do rewrite constant_family_include.
by rewrite (map_comp (fun i => form_include (alpha i)) (cast_ord (size_nseq m p))) cast_enum.
Qed.
End ConstantFamily.
(** Source for [ones_sum]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma ones_sum m : sumn (nseq m 1%N) = m.
Proof. by rewrite sumn_nseq mul1n. Qed.
