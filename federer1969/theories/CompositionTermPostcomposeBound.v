(** Federer (1969), 3.1.24, pp. 239–240: bound
    one composition term after applying the inverse first
    derivative. Exact factorial weights are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom Bilinear HomogeneousHom BoundedHom RealNormUP SymmetricAlgebra SymmetricForms
  SymmetricFormExtension SymmetricFormPostcompose SymmetricFormSum SymmetricOperatorNormUP SymmetricOperatorNorm
  SymmetricOperatorWordBound SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials
  CompositionMultiIndices CompositionFormMonomials CompositionFormCoefficient CompositionWordNormBound
  ScalarCompositionCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [composition_form_term_postcompose_bound]: supporting
    the inverse derivative bound in Federer 3.1.24, pp. 239–240.
    Inner forms have finite bounds C_i, the outer form has
    bound B, and a linear postcomposition has bound l. Binary
    shuffles give p! l B/alpha! times the monomial in
    C_i/i!. This holds on arbitrary unit tuples, so it
    controls the operator norm without a polarization loss. *)
Theorem composition_form_term_postcompose_bound (R:realType) (X Y Z T:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ) (hNT:is_real_norm NT)
    k p (phi:forall i,S_m X Y i) (psi:forall i,S_m Y Z i) (C:'I_k->R)
    (L:Hom Z T) l B (a:composition_indices k p) (t:p.-tuple X) :
  (forall i,0<=C i) ->
  (forall i,(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E) ->
  0<=l -> 0<=B -> (forall z,NT (L z)<=l*NZ z) ->
  (symmetric_operator_norm hNY.1 NZ (psi (symmetric_multi_degree (composition_indices_unbound a)))<=B%:E)%E ->
  symmetric_form_unit_tuple NX t ->
  NT (L (@composition_differential_form_term R X Y Z k phi psi p a t))<=
    (p`!)%:R*(l*B/(symmetric_multi_factorial (composition_indices_unbound a))%:R)*
      symmetric_scalar_monomial (fun i:'I_k=>C i/((val i).+1`!)%:R) (composition_indices_unbound a).
Proof.
move=>hC hPhi hl hB hL hPsi ht.
pose alpha:=composition_indices_unbound a.
pose w:=symmetric_monomial_word (fun i:'I_k=>i) alpha.
pose d:=symmetric_multi_degree alpha.
pose P:=hom_comp L (sform_homogeneous (psi d)).
pose M:=l*B.
have hM:0<=M:=mulr_ge0 hl hB.
have hlen:size w=d:=symmetric_monomial_word_size (fun i:'I_k=>i) alpha.
have hdegree:(\sum_(i<-w) (val i).+1)%N= p.
  by rewrite /w composition_weighted_word_degree composition_indices_weight.
have hP ys (hys:size ys=size w):NT (P (symmetric_word ys))<=M*\prod_(y<-ys) NY y.
  have hs:size ys=d by rewrite hys hlen.
  have hb:=@symmetric_operator_finite_word_bound R Y Z NY NZ hNY hNZ.1 d (psi d) B hPsi ys hs.
  rewrite /P hom_compE.
  apply:le_trans (hL _) _.
  have hh:=ler_wpM2l hl hb.
  change (is_true (l*NZ (sform_homogeneous (psi d) (symmetric_word ys))<=l*(B*\prod_(y<-ys) NY y))) in hh.
  have he:l*(B*\prod_(y<-ys) NY y)=M*\prod_(y<-ys) NY y by rewrite /M mulrA.
  by rewrite he in hh.
pose tw:=tcast (esym hdegree) t.
have htw:symmetric_form_unit_tuple NX tw.
  move=>i; rewrite /tw tcastE; exact:ht.
have hb:=@composition_form_word_operator_bound R X Y T NX NY NT hNX hNY hNT k phi C
  hC hPhi w P M hM hP tw htw.
rewrite /tw val_tcast hdegree in hb.
have hprod:(\prod_(i<-w) (C i/((val i).+1`!)%:R))=
    symmetric_scalar_monomial (fun i:'I_k=>C i/((val i).+1`!)%:R) alpha.
  have hh:=symmetric_scalar_word_product (fun i:'I_k=>C i/((val i).+1`!)%:R) alpha.
  have hmap:=@symmetric_monomial_word_map 'I_k R k (fun i=>i) alpha
    (fun i=>C i/((val i).+1`!)%:R).
  by rewrite -hmap big_map in hh.
rewrite hprod in hb.
rewrite /composition_differential_form_term sform_scaleE symmetric_form_postcomposeE hom_as_linearE
  (linZ (hom_linear L)) sform_componentE /composition_form_monomial
  (real_seminorm_scale hNT.1) normfV normr_nat.
have hinv:0<=((symmetric_multi_factorial alpha)%:R:R)^-1 by rewrite invr_ge0 ler0n.
apply:le_trans (ler_wpM2l hinv hb) _.
pose A:R:=(symmetric_multi_factorial alpha)%:R^-1.
pose Q:=symmetric_scalar_monomial (fun i:'I_k=>C i/((val i).+1`!)%:R) alpha.
change (A*((p`!)%:R*M*Q)<=(p`!)%:R*(l*B*A)*Q).
have he:A*((p`!)%:R*M*Q)=(p`!)%:R*(l*B*A)*Q by rewrite /M; ring.
by rewrite he.
Qed.
