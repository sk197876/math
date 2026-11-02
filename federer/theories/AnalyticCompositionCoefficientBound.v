(** Federer (1969), 3.1.24, p. 239: the
    exact operator norm bound for the higher composition coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom Bilinear HomogeneousHom BoundedHom RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormExtension SymmetricFormPostcompose SymmetricFormSum SymmetricOperatorNormUP SymmetricOperatorNorm
  SymmetricOperatorWordBound SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials
  CompositionMultiIndices CompositionPositiveDegree CompositionFormMonomials CompositionFormCoefficient
  CompositionWordNormBound ScalarAnalyticCompositionSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_composition_form_operator_bound]: the
    first displayed bound for D^p(g composed with f) in
    Federer 3.1.24, p. 239. Bounds c^m m! and
    gamma^m m! for the inner and outer derivative forms
    imply c^p gamma(gamma+1)^(p-1) p! for the
    actual composition coefficient. Binary shuffles prove the
    factorial norm estimate; the exact weighted sum is
    evaluated by the printed scalar rational special case. *)
Theorem analytic_composition_form_operator_bound (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    p (phi:forall i,S_m X Y i) (psi:forall j,S_m Y T j) c g :
  (1<=p)%N -> 0<=c -> 0<=g ->
  (forall m,(1<=m<=p)%N ->
    (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E) ->
  (forall j,(1<=j<=p)%N ->
    (symmetric_operator_norm hNY.1 NT (psi j)<=(g^+j*(j`!)%:R)%:E)%E) ->
  (symmetric_operator_norm hNX.1 NT
    (@composition_differential_form_coefficient R X Y T p phi psi p)<=
      (c^+p*g*(g+1)^+(p-1)*(p`!)%:R)%:E)%E.
Proof.
move=>hp hc hg hphi hpsi.
pose C (i:'I_p):=c^+(val i).+1*((val i).+1`!)%:R.
have hC i:0<=C i by exact (mulr_ge0 (exprn_ge0 (val i).+1 hc) (ler0n _ _)).
have hCphi i:(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E.
  apply: hphi; apply/andP; split; first by [].
  exact (valP i).
apply: (proj2 (symmetric_operator_norm_bound hNX.1 NT _ _))=>t ht.
have hterm (a:composition_indices p p):
    NT (@composition_differential_form_term R X Y T p phi psi p a t)<=
      ((p`!)%:R*c^+p)*
        ((g^+(symmetric_multi_degree (composition_indices_unbound a))*
          (symmetric_multi_degree (composition_indices_unbound a))`!%:R)/
          (symmetric_multi_factorial (composition_indices_unbound a))%:R).
  pose alpha:=composition_indices_unbound a.
  pose w:=symmetric_monomial_word (fun i:'I_p=>i) alpha.
  pose d:=symmetric_multi_degree alpha.
  pose L:=sform_homogeneous (psi d).
  pose M:=g^+d*(d`!)%:R.
  have hd0:(1<=d)%N:=composition_indices_positive_outer_degree a hp.
  have hdp:(d<=p)%N:=composition_indices_outer_degree a.
  have hM:0<=M by exact (mulr_ge0 (exprn_ge0 d hg) (ler0n _ _)).
  have hPsi:(symmetric_operator_norm hNY.1 NT (psi d)<=M%:E)%E.
    apply: hpsi; by rewrite hd0 hdp.
  have hlen:size w=d:=symmetric_monomial_word_size (fun i:'I_p=>i) alpha.
  have hdegree:(\sum_(i<-w) (val i).+1)%N= p.
    by rewrite /w composition_weighted_word_degree composition_indices_weight.
  have hL ys (hys:size ys=size w):NT (L (symmetric_word ys))<=M*\prod_(y<-ys) NY y.
    apply: (@symmetric_operator_finite_word_bound R Y T NY NT hNY hNT.1 d (psi d) M hPsi ys).
    by rewrite hys hlen.
  pose tw:=tcast (esym hdegree) t.
  have htw:symmetric_form_unit_tuple NX tw.
    move=>i; rewrite /tw tcastE; exact: ht.
  have hb:=@composition_form_word_operator_bound R X Y T NX NY NT hNX hNY hNT p phi C
    hC hCphi w L M hM hL tw htw.
  rewrite /tw val_tcast hdegree in hb.
  have hprod:(\prod_(i<-w) (C i/((val i).+1`!)%:R))= c^+p.
    have he:(\prod_(i<-w) (C i/((val i).+1`!)%:R))=
        c^+(\sum_(i<-w) (val i).+1)%N.
      rewrite expr_sum; apply: eq_bigr=>i _.
      rewrite /C mulfK; first reflexivity.
      by rewrite pnatr_eq0 -lt0n fact_gt0.
    by rewrite hdegree in he.
  rewrite hprod in hb.
  rewrite /composition_differential_form_term sform_scaleE symmetric_form_postcomposeE
    hom_as_linearE sform_componentE /composition_form_monomial
    (real_seminorm_scale hNT.1) normfV normr_nat.
  have hinv:0<=((symmetric_multi_factorial alpha)%:R:R)^-1 by rewrite invr_ge0 ler0n.
  apply: le_trans (ler_wpM2l hinv hb) _.
  change ((symmetric_multi_factorial alpha)%:R^-1*((p`!)%:R*M*c^+p)<=
    ((p`!)%:R*c^+p)*(M/(symmetric_multi_factorial alpha)%:R)).
  have heq:(symmetric_multi_factorial alpha)%:R^-1*((p`!)%:R*M*c^+p)=
      ((p`!)%:R*c^+p)*(M/(symmetric_multi_factorial alpha)%:R) by ring.
  by rewrite heq.
have hEval:linear (fun F:S_m X T p=>F t).
  move=>a F G; by rewrite sform_addE sform_scaleE.
pose E:=@HomMap R (S_m X T p) T (fun F=>F t) (introT (asboolP _) hEval).
have hsum:(\sum_(a:composition_indices p p)
      @composition_differential_form_term R X Y T p phi psi p a) t=
    \sum_(a:composition_indices p p) @composition_differential_form_term R X Y T p phi psi p a t.
  change (E (\sum_(a:composition_indices p p)
      @composition_differential_form_term R X Y T p phi psi p a)=
    \sum_(a:composition_indices p p) E (@composition_differential_form_term R X Y T p phi psi p a)).
  by rewrite linear_sum.
rewrite /composition_differential_form_coefficient hsum.
apply: le_trans (real_seminorm_sum hNT.1 _) _.
have htotal:(\sum_(a:composition_indices p p)
    NT (@composition_differential_form_term R X Y T p phi psi p a t))<=
    \sum_(a:composition_indices p p) ((p`!)%:R*c^+p)*
      ((g^+(symmetric_multi_degree (composition_indices_unbound a))*
        (symmetric_multi_degree (composition_indices_unbound a))`!%:R)/
        (symmetric_multi_factorial (composition_indices_unbound a))%:R).
  apply: ler_sum=>a _; exact (hterm a).
apply: le_trans htotal _.
rewrite -big_distrr (analytic_composition_scalar_sum hg hp).
change (((p`!)%:R*c^+p)*(g*(g+1)^+(p-1))<=
  c^+p*g*(g+1)^+(p-1)*(p`!)%:R).
have heq:((p`!)%:R*c^+p)*(g*(g+1)^+(p-1))=
    c^+p*g*(g+1)^+(p-1)*(p`!)%:R by ring.
by rewrite heq.
Qed.
