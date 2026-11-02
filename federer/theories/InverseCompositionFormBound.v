(** Federer (1969), 3.1.24, pp. 239–240: the
    lower-order inverse majorant bounds the highest differential
    through the exact composition identity and shuffle estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom Bilinear HomogeneousHom BoundedHom RealNormUP RealSeminormFilteredSum
  SymmetricAlgebra SymmetricForms SymmetricFormPostcompose SymmetricOperatorNormUP SymmetricOperatorNorm
  SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices CompositionLinearIndex
  CompositionRemainderFilter CompositionFormCoefficient CompositionLinearTermInverse
  CompositionTermPostcomposeBound InverseMajorantUP InverseRemainderMonomialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_composition_form_bound]: supporting
    the induction ||D^p f||<=lambda_p p! in Federer
    3.1.24, pp. 239–240. The composition has zero pth
    form for p>=2. Its outer first derivative has a bounded
    left inverse L. Separate that term and bound every
    remainder monomial using only strictly lower inner orders.
    The finite bound for the highest inner form is used only
    to apply the general word estimate and drops out because
    its exponent in every remainder term is zero. *)
Theorem inverse_composition_form_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    p (phi:forall i,S_m X Y i) (psi:forall i,S_m Y X i)
    (C:'I_p->R) (lambda:nat->R) g (L:Hom X Y) :
  (2<=p)%N -> 0<=g -> (forall m,0<=lambda m) ->
  (forall i,0<=C i) ->
  (forall i,(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E) ->
  (forall i,((val i).+1<p)%N -> C i<=lambda (val i).+1*((val i).+1`!)%:R) ->
  (forall j,(2<=j<=p)%N -> (symmetric_operator_norm hNY.1 NX (psi j)<=(g^+j*(j`!)%:R)%:E)%E) ->
  (forall x,NY (L x)<=lambda 1%N*NX x) ->
  (forall y,L (SymmetricFormExtension.sform_homogeneous (psi 1%N) (symmetric_generator y))=y) ->
  @composition_differential_form_coefficient R X Y X p phi psi p=0 ->
  (symmetric_operator_norm hNX.1 NY (phi p)<=
    (lambda 1%N*(p`!)%:R*inverse_majorant_remainder g lambda p)%:E)%E.
Proof.
move=>hp hg hLambda hC hPhi hLower hPsi hL hInv hComp.
have hp1:(1<=p)%N:=leq_trans (leqnSn 1%N) hp.
have [z hz]:=composition_degree_one_exists hp1.
apply:(proj2 (symmetric_operator_norm_bound hNX.1 NY _ _))=>t ht.
pose term (a:composition_indices p p):= @composition_differential_form_term R X Y X p phi psi p a.
have hEval:linear (fun F:S_m X X p=>L (F t)).
  move=>c F G; rewrite sform_addE sform_scaleE.
  by rewrite (linD (hom_linear L)) (linZ (hom_linear L)).
pose E:=@HomMap R (S_m X X p) Y (fun F=>L (F t)) (introT (asboolP _) hEval).
have hSum:L ((@composition_differential_form_coefficient R X Y X p phi psi p) t)=
    \sum_(a:composition_indices p p) L (term a t).
  change (E (\sum_(a:composition_indices p p) term a)=\sum_(a:composition_indices p p) E (term a)).
  by rewrite linear_sum.
have hTerm:=@composition_linear_term_left_inverse R (@pchar_num R) X Y p phi psi L z hInv hz.
have hLinear:L (term z t)=phi p t.
  have hh:=congr1 (fun F:S_m X Y p=>F t) hTerm.
  by rewrite symmetric_form_postcomposeE hom_as_linearE in hh.
rewrite hComp sform_zeroE (bigD1 z) // hLinear in hSum.
rewrite (lin0 (hom_linear L)) in hSum.
pose S:=\sum_(a:composition_indices p p | a!=z) L (term a t).
have hEq:phi p t= -S.
  have hh:=congr1 (fun y:Y=>y-S) (esym hSum).
  change (phi p t+S-S=0-S) in hh.
  by rewrite addrK sub0r in hh.
rewrite hEq (real_seminorm_negate hNY.1).
apply:le_trans (@real_seminorm_filtered_sum R Y NY hNY.1 (composition_indices p p)
  (fun a=>a!=z) (fun a=>L (term a t))) _.
have hIndex:(\sum_(a:composition_indices p p | a!=z) NY (L (term a t)))=
    \sum_(a:composition_indices p p | (1<symmetric_multi_degree (composition_indices_unbound a))%N)
      NY (L (term a t)).
  apply:eq_bigl=>a; exact (composition_remainder_filter a hp1 hz).
rewrite hIndex.
pose cost (a:composition_indices p p):R:=
    (g^+(symmetric_multi_degree (composition_indices_unbound a)))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R/
      (symmetric_multi_factorial (composition_indices_unbound a))%:R*
    \prod_(i<p) lambda (val i).+1^+(composition_indices_unbound a i).
have hTermBound (a:composition_indices p p)
    (ha:(1<symmetric_multi_degree (composition_indices_unbound a))%N):
    NY (L (term a t))<=((p`!)%:R*lambda 1%N)*cost a.
  pose d:=symmetric_multi_degree (composition_indices_unbound a).
  have hd:(2<=d<=p)%N by rewrite ha (composition_indices_outer_degree a).
  have hB:0<=g^+d*(d`!)%:R:=mulr_ge0 (exprn_ge0 d hg) (ler0n _ _).
  have hb:=@composition_form_term_postcompose_bound R X Y X Y NX NY NX NY hNX hNY hNX hNY
    p p phi psi C L (lambda 1%N) (g^+d*(d`!)%:R) a t hC hPhi (hLambda 1%N) hB hL (hPsi d hd) ht.
  have hm:=@inverse_remainder_normalized_monomial_bound R p p a C lambda ha hC hLambda hLower.
  have hfac:0<=(symmetric_multi_factorial (composition_indices_unbound a))%:R :>R:=ler0n _ _.
  have hScale:0<=(p`!)%:R*(lambda 1%N*(g^+d*(d`!)%:R)/
      (symmetric_multi_factorial (composition_indices_unbound a))%:R).
    exact (mulr_ge0 (ler0n _ _) (divr_ge0 (mulr_ge0 (hLambda 1%N) hB) hfac)).
  apply:le_trans hb _.
  apply:le_trans (ler_wpM2l hScale hm) _.
  rewrite /symmetric_scalar_monomial /cost -/d.
  pose A:R:=g^+d*(d`!)%:R.
  pose B:R:=(symmetric_multi_factorial (composition_indices_unbound a))%:R^-1.
  pose P:R:=\prod_(i<p) lambda (val i).+1^+(composition_indices_unbound a i).
  change ((p`!)%:R*(lambda 1%N*A*B)*P<=((p`!)%:R*lambda 1%N)*(A*B*P)).
  have he:(p`!)%:R*(lambda 1%N*A*B)*P=((p`!)%:R*lambda 1%N)*(A*B*P) by ring.
  by rewrite he.
have hTotal:(\sum_(a:composition_indices p p |
    (1<symmetric_multi_degree (composition_indices_unbound a))%N) NY (L (term a t)))<=
    \sum_(a:composition_indices p p |
      (1<symmetric_multi_degree (composition_indices_unbound a))%N) ((p`!)%:R*lambda 1%N)*cost a.
  apply:ler_sum=>a ha; exact (hTermBound a ha).
apply:le_trans hTotal _.
rewrite -big_distrr.
change (((p`!)%:R*lambda 1%N)*inverse_majorant_remainder g lambda p<=
  lambda 1%N*(p`!)%:R*inverse_majorant_remainder g lambda p).
by rewrite [(p`!)%:R*lambda 1%N]mulrC.
Qed.
