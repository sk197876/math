(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import Convolution AlternatingProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, binary shuffle formula. The two argument tuples are
    obtained by applying the shuffle and taking its two consecutive blocks. *)
Section ShuffleArguments.
Variable K : fieldType.
Variable V : lmodType K.
Variables p q : nat.
(** Source for [shuffle_left_values]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Definition or construction used to formalise this
    passage. *)
Definition shuffle_left_values (t : (p+q).-tuple V) (sigma : 'S_(p+q)) :=
  [seq nth 0 t i | i <- take p (map val (permutation_sequence sigma))].
(** Source for [shuffle_right_values]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Definition or construction used to formalise this
    passage. *)
Definition shuffle_right_values (t : (p+q).-tuple V) (sigma : 'S_(p+q)) :=
  [seq nth 0 t i | i <- drop p (map val (permutation_sequence sigma))].
(** Source for [shuffle_left_size]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma shuffle_left_size t sigma : size (shuffle_left_values t sigma) == p.
Proof. by rewrite /shuffle_left_values size_map size_take_min size_map size_tuple (minn_idPl (leq_addr q p)). Qed.
(** Source for [shuffle_right_size]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma shuffle_right_size t sigma : size (shuffle_right_values t sigma) == q.
Proof. by rewrite /shuffle_right_values size_map size_drop size_map size_tuple addKn. Qed.
(** Source for [shuffle_left_tuple]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Definition or construction used to formalise this
    passage. *)
Definition shuffle_left_tuple t sigma : p.-tuple V := Tuple (shuffle_left_size t sigma).
(** Source for [shuffle_right_tuple]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Definition or construction used to formalise this
    passage. *)
Definition shuffle_right_tuple t sigma : q.-tuple V := Tuple (shuffle_right_size t sigma).
End ShuffleArguments.

Section BinaryFormula.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variables p q : nat.
Variables (a : A_m V W p) (b : A_m V W q).
Local Notation A := (form_homogeneous a).
Local Notation B := (form_homogeneous b).
Local Notation T := (paired_tensor hmu A B).
(** Source for [paired_shuffle_term]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma paired_shuffle_term s i n (sigma : 'S_n) :
  T (shuffle_term_fun s i sigma) = FedererPermutation.index K sigma *:
    mu (form_words a [seq nth 0 s j | j <- take i (map val (permutation_sequence sigma))])
       (form_words b [seq nth 0 s j | j <- drop i (map val (permutation_sequence sigma))]).
Proof.
rewrite /shuffle_term_fun linearZ paired_tensorE !form_homogeneousE !form_extensionE.
by [].
Qed.
(** Source for [paired_shuffle_wrong]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma paired_shuffle_wrong s n (i : 'I_n.+1) (sigma : 'S_n) :
  (i : nat) != p -> T (shuffle_term_fun s i sigma) = 0.
Proof.
move=> hi; rewrite paired_shuffle_term.
have hs : size [seq nth 0 s j | j <- take i (map val (permutation_sequence sigma))] != p.
  have hin : (i <= n)%N by move: (ltn_ord i); rewrite ltnS.
  by rewrite size_map size_take_min size_map size_tuple (minn_idPl hin).
by rewrite (form_words_wrong a hs) (bil0l hmu) scaler0.
Qed.
(** Source for [form_wedge_shuffle]: Federer (1969), 1.4.2, p. 18, binary
    shuffle formula. In words: The product of a p-form and a q-form is
    evaluated by summing signed products of their evaluations over all
    (p,q)-shuffles. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem form_wedge_shuffle (t : (p+q).-tuple V) :
  form_wedge h2 hmu a b t = \sum_(sigma : Sh p q)
    FedererPermutation.index K (val sigma) *:
      mu (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma))).
Proof.
rewrite form_wedgeE Psi_shuffle_frame linear_sum.
under eq_bigr do rewrite linear_sum.
rewrite size_tuple.
have hp : (p < (p+q).+1)%N by rewrite ltnS leq_addr.
pose ip : 'I_(p+q).+1 := Ordinal hp.
rewrite (bigD1 ip) //=.
have hz : (\sum_(i : 'I_(p+q).+1 | i != ip)
    \sum_(sigma : {sigma : 'S_(p+q) | shuffle_in i sigma})
      T (shuffle_term_fun t i (val sigma))) = 0.
  apply: big1 => i hi; apply: big1 => sigma _.
  apply: paired_shuffle_wrong; by move: hi; rewrite -val_eqE.
rewrite hz addr0; apply: eq_bigr => sigma _; rewrite paired_shuffle_term.
change (FedererPermutation.index K (val sigma) *:
    mu (form_words a (shuffle_left_tuple t (val sigma)))
       (form_words b (shuffle_right_tuple t (val sigma))) =
  FedererPermutation.index K (val sigma) *:
    mu (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma)))).
by rewrite !form_wordsE.
Qed.
End BinaryFormula.
