(** Federer (1969), 3.1.24, p. 239: the
    operator estimate for a word of inner differentials,
    expanded by the binary shuffle formula of 1.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal fingroup perm ring.
From Federer Require Import TensorUP Hom Bilinear HomogeneousHom BoundedHom RealNormUP
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormUnit SymmetricFormSum
  SymmetricFormPostcompose SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricOperatorProductBound
  Shuffles AlternatingShuffle ShuffleCardinalityBound CompositionFormMonomials CompositionWordTuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [composition_form_word_operator_bound]: supporting
    the bound for every term of S(p) in Federer
    3.1.24, p. 239. Postcompose a word of inner
    derivative forms with an outer linear functional whose
    values on words of the prescribed length have product
    bound M. Binary shuffles give the total-degree factorial
    divided by the product of inner degree factorials. This
    retains arbitrary input tuples and the operator norm;
    no norm on the auxiliary symmetric algebra is imposed. *)
Theorem composition_form_word_operator_bound (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    k (phi:forall i,S_m X Y i) (C:'I_k->R) :
  (forall i,0<=C i) ->
  (forall i,(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E) ->
  forall s:seq 'I_k,forall (L:Hom (symmetric_space Y) T) M,
    0<=M ->
    (forall ys:seq Y,size ys=size s -> NT (L (symmetric_word ys))<=M*\prod_(y<-ys) NY y) ->
    forall t:(\sum_(i<-s) (val i).+1)%N.-tuple X,
      symmetric_form_unit_tuple NX t ->
      NT (L (@composition_form_word R X Y k phi s (symmetric_word t)))<=
        ((\sum_(i<-s) (val i).+1)%N`!)%:R*M*
          \prod_(i<-s) (C i/((val i).+1`!)%:R).
Proof.
move=>hC hphi; elim=>[|i s ih] L M hM hL t ht.
- move:t ht; rewrite !big_nil=>t ht.
  have ht0:t= [tuple].
    apply: eq_from_tnth=>j; by case:j=>j.
  rewrite ht0 /composition_form_word symmetric_word_nil symmetric_coefficient_formE
    symmetric_augmentation_unit scale1r /= fact0 mul1r mulr1.
  have hh:=hL [::] erefl.
  by rewrite symmetric_word_nil big_nil mulr1 in hh.
- move:t ht; rewrite !big_cons=>t ht.
  pose d:=(val i).+1.
  pose P:=(\sum_(j<-s) (val j).+1)%N.
  pose A:=\prod_(j<-s) (C j/((val j).+1`!)%:R).
  have hA:0<=A.
    apply: prodr_ge0=>j _; apply: divr_ge0; first exact (hC j).
    exact: ler0n.
  pose B:=(P`!)%:R*M*C i*A.
  have hB:0<=B.
    exact (mulr_ge0 (mulr_ge0 (mulr_ge0 (ler0n _ _) hM) (hC i)) hA).
  rewrite composition_form_word_tuple_successor linear_sum.
  apply: le_trans (real_seminorm_sum hNT.1 _) _.
  have hsum:(\sum_(sigma:Sh d P)
      NT (L (symmetric_product
        (symmetric_generator (phi d (shuffle_left_tuple t (val sigma))))
        (@composition_form_word R X Y k phi s (symmetric_word (shuffle_right_tuple t (val sigma)))))))<=
      \sum_(sigma:Sh d P) B.
    apply: ler_sum=>sigma _.
    pose y:=phi d (shuffle_left_tuple t (val sigma)).
    have hy:NY y<=C i.
      exact ((symmetric_operator_norm_bound hNX.1 NY (phi d) (C i)).1 (hphi i)
        (shuffle_left_tuple t (val sigma)) (@symmetric_shuffle_left_unit R X NX d P t (val sigma) ht)).
    have hlin:linear (fun z=>L (symmetric_product (symmetric_generator y) z)).
      move=>a u v; rewrite (symmetric_product_bilinear Y).2 (hom_linear L); reflexivity.
    pose Ly:=@HomMap R (symmetric_space Y) T
      (fun z=>L (symmetric_product (symmetric_generator y) z)) (introT (asboolP _) hlin).
    have hMy:0<=M*NY y:=mulr_ge0 hM (real_seminorm_nonnegative hNY.1 y).
    have hLy ys (hys:size ys=size s):NT (Ly (symmetric_word ys))<=
        (M*NY y)*\prod_(z<-ys) NY z.
      have hlen:size (y::ys)=size (i::s) by rewrite /= hys.
      have hh:=hL (y::ys) hlen.
      rewrite symmetric_word_cons big_cons in hh.
      have heq:M*(NY y*\prod_(z<-ys) NY z)= (M*NY y)*\prod_(z<-ys) NY z by ring.
      by rewrite heq in hh.
    have hb:=ih Ly (M*NY y) hMy hLy (shuffle_right_tuple t (val sigma))
      (@symmetric_shuffle_right_unit R X NX d P t (val sigma) ht).
    change (NT (Ly (@composition_form_word R X Y k phi s
      (symmetric_word (shuffle_right_tuple t (val sigma)))))<=B).
    apply: le_trans hb _.
    have hfac:0<=(P`!)%:R*M*A:=mulr_ge0 (mulr_ge0 (ler0n _ _) hM) hA.
    have hmul:=ler_wpM2l hfac hy.
    have heq1:(P`!)%:R*(M*NY y)*A= ((P`!)%:R*M*A)*NY y by ring.
    have heq2:B= ((P`!)%:R*M*A)*C i by rewrite /B; ring.
    by rewrite heq1 heq2.
  apply: le_trans hsum _.
  have hcount:(\sum_(sigma:Sh d P) B)= (#|{:Sh d P}|%:R:R)*B.
    by rewrite sumr_const -(mulr_natl B _) cardT.
  rewrite hcount.
  have hc:(#|{:Sh d P}|%:R:R)<=('C(d+P,d)%:R:R).
    rewrite ler_nat; exact: shuffle_cardinality_bound.
  apply: le_trans (ler_wpM2r hB hc) _.
  have hdne:((d`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  have hbin:('C(d+P,d)%:R:R)*((d`!)%:R*(P`!)%:R)= ((d+P)`!)%:R.
    rewrite -!natrM.
    have hh:=bin_fact (leq_addr P d); by rewrite addKn in hh; rewrite hh.
  have hratio:('C(d+P,d)%:R:R)*(P`!)%:R= ((d+P)`!)%:R/(d`!)%:R.
    rewrite -hbin; field; exact hdne.
  have heq:('C(d+P,d)%:R:R)*B= ((d+P)`!)%:R*M*(C i/(d`!)%:R)*A.
    have hreg:('C(d+P,d)%:R:R)*B=
        (('C(d+P,d)%:R:R)*(P`!)%:R)*M*C i*A by rewrite /B; ring.
    rewrite hreg hratio; ring.
  rewrite heq /=.
  have heq2:((d+P)`!)%:R*M*(C i/(d`!)%:R)*A=
      ((d+P)`!)%:R*M*((C i/(d`!)%:R)*A) by ring.
  by rewrite heq2.
Qed.
