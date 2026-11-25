(** Federer (1969), 4.1.6, pp. 352–353: the signed
    first-slot product formula with arbitrary coefficients.
    This specialization of the existing exterior diagonal
    uses the original homogeneous mixed tensor pairing;
    the shuffle identity itself is the earlier 1.3.3 result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm.
From Federer Require Import Hom TensorUP Bilinear Alternating AlternatingForms
  AlternatingWords AlternatingIsomorphism AlternatingShuffle
  MixedTensorPairing MixedHomogeneousConvolution MixedAlternatingProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section MixedAlternatingShuffle.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V W1 W2 W3:lmodType K.
Variable B:W1->W2->W3.
Hypothesis hB:bilinear B.
Variables p q:nat.
Variables (a:A_m V W1 p) (b:A_m V W2 q).
Local Notation T := (mixed_paired_tensor hB (form_homogeneous a) (form_homogeneous b)).

(** Source for [mixed_paired_shuffle_term]: evaluate the
    original diagonal shuffle through the mixed pairing,
    supporting Federer 4.1.6, pp. 352–353. *)
Lemma mixed_paired_shuffle_term s i n (sigma:'S_n):
  T (shuffle_term_fun s i sigma)=FedererPermutation.index K sigma *:
    B (form_words a [seq nth 0 s j|j<-take i (map val (permutation_sequence sigma))])
      (form_words b [seq nth 0 s j|j<-drop i (map val (permutation_sequence sigma))]).
Proof.
rewrite /shuffle_term_fun linearZ mixed_paired_tensorE !form_homogeneousE !form_extensionE.
reflexivity.
Qed.

(** Source for [mixed_paired_shuffle_wrong]: homogeneity
    removes the other diagonal degrees, supporting
    Federer 4.1.6, pp. 352–353. *)
Lemma mixed_paired_shuffle_wrong s n (i:'I_n.+1) (sigma:'S_n):
  (i:nat)!=p ->T (shuffle_term_fun s i sigma)=0.
Proof.
move=>hi; rewrite mixed_paired_shuffle_term.
have hs:size [seq nth 0 s j|j<-take i (map val (permutation_sequence sigma))]!=p.
  have hin:(i<=n)%N by move:(ltn_ord i); rewrite ltnS.
  by rewrite size_map size_take_min size_map size_tuple (minn_idPl hin).
by rewrite (form_words_wrong a hs) (bil0l hB) scaler0.
Qed.

(** Source for [mixed_form_product_shuffle]: the original
    1.4.2 alternating formula, now through the mixed
    coefficient pairing used in Federer 4.1.6,
    pp. 352–353. *)
Theorem mixed_form_product_shuffle (t:(p+q).-tuple V):
  mixed_form_product h2 hB a b t=\sum_(sigma:Sh p q)
    FedererPermutation.index K (val sigma) *:
      B (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma))).
Proof.
rewrite mixed_form_product_tuple Psi_shuffle_frame linear_sum.
under eq_bigr do rewrite linear_sum.
rewrite size_tuple.
have hp:(p<(p+q).+1)%N by rewrite ltnS leq_addr.
pose ip:'I_(p+q).+1:=Ordinal hp.
rewrite (bigD1 ip) //=.
have hz:(\sum_(i:'I_(p+q).+1|i!=ip)
    \sum_(sigma:{sigma:'S_(p+q)|shuffle_in i sigma}) T (shuffle_term_fun t i (val sigma)))=0.
  apply:big1=>i hi; apply:big1=>sigma _.
  apply:mixed_paired_shuffle_wrong; by move:hi; rewrite -val_eqE.
rewrite hz addr0; apply:eq_bigr=>sigma _; rewrite mixed_paired_shuffle_term.
change (FedererPermutation.index K (val sigma) *:
    B (form_words a (shuffle_left_tuple t (val sigma))) (form_words b (shuffle_right_tuple t (val sigma)))=
  FedererPermutation.index K (val sigma) *:
    B (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma)))).
by rewrite !form_wordsE.
Qed.
End MixedAlternatingShuffle.
