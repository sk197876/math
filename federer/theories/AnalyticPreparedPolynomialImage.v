(** Federer (1969), 3.4.7, p. 325: the
    polynomial supplied by preparation belongs to the original
    transverse polynomial subring. Its actual coefficients are
    monic and vanish at the transverse origin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormAnalyticUP NormRegularity
  NormClassZeroTopology NormAnalyticLocal LocalGermUP LocalGermSealed AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueUP AnalyticGermValueSealed
  WeierstrassTransverseUP WeierstrassTransversePullback WeierstrassPreparationUP
  WeierstrassFiniteFamilyExtension AnalyticTransversePolynomialRepresentative
  CommutativePolynomialUP CommutativePolynomialFiniteSums
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PreparedImage.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Hypothesis hXiValues:forall x,analytic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Local Notation value:=(@AnalyticGermValue.map R K NK hNK (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [analytic_prepared_polynomial_image]: the
    original prepared W is the image of a monic
    distinguished polynomial in the transverse germ ring,
    expanding the subring assertion of 3.4.7, p. 325.
    The representatives are those of preparation, and their
    neighbourhood equation proves the identification. *)
Theorem analytic_prepared_polynomial_image k (W:G)
    (Wi:'I_k->@analytic_germ_ring R K NK hNK 0):
  @is_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W Wi ->
  exists P:B,is_distinguished_polynomial coefficient value P k /\J P = W.
Proof.
move=>[w [hW [a [hA [hZero [U [haU [hw hValuesW]]]]]]]].
have hAnalytic i:@norm_analytic_at R K R^o NK (fun t=>`|t|) hNK
    (@scalar_absolute_value_norm R) setT (analytic_representative_value (a i)) (projection 0).
  rewrite (linear0 projection);exact:analytic_representative_analytic (a i).
pose converted i:@analytic_representative_type R K NK hNK (projection 0):=
  exist _ (analytic_representative_value (a i)) (hAnalytic i).
pose oneRep:=@analytic_constant_representative R K NK hNK (projection 0) 1.
have [d hD]:=@weierstrass_finite_family_extension
  (@analytic_representative_type R K NK hNK (projection 0)) k converted oneRep.
pose c i:=if i==k then oneRep else d i.
pose P:=\sum_(i<k.+1) embed (analytic_germ (c i))*variable^+i.
have hCoefficient i:coefficient P i = if (i<k.+1)%N then (analytic_germ (c i):A) else 0.
  exact:(@polynomial_finite_expression_coefficient A B embed variable coefficient hP
    k.+1 (fun i=>analytic_germ (c i)) i).
have hLeading:coefficient P k = 1 by rewrite hCoefficient ltnSn /c eqxx.
have hSupport i (hi:(k<i)%N):coefficient P i = 0.
  rewrite hCoefficient;have hLarge:(k.+1<=i)%N:=hi.
  by rewrite (leq_gtF hLarge).
have hDistinguished:is_distinguished_polynomial coefficient value P k.
  split.
  - split;last exact:hLeading.
    split;last exact:hSupport.
    rewrite hLeading;move=>h;have hOne:(1:A)!=0:=oner_neq0 A;by rewrite h eqxx in hOne.
  - move=>i hi.
    have hBound:(i<k.+1)%N:=ltn_trans hi (ltnSn k).
    have hNe:(i==k) = false:=ltn_eqF hi.
    rewrite hCoefficient hBound /c hNe (@AnalyticGermValue.laws R K NK hNK (projection 0)).
    have hDi:=hD (Ordinal hi).
    change (d i=converted (Ordinal hi)) in hDi.
    rewrite hDi /converted /analytic_representative_value /= (linear0 projection).
    exact:hZero.
have [f [hValuesF hGermF]]:=@analytic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k.+1 c hXiValues.
have hEval:J P = analytic_germ f.
  rewrite hGermF (@polynomial_evaluation_finite_expression A B G embed variable coefficient
    hP E Gamma J hJ P k.+1 hSupport).
  apply:eq_bigr=>i _;by rewrite hCoefficient (ltn_ord i).
have hGerms:analytic_germ f=analytic_germ w.
  pose TX:=Topological.clone (real_norm_metric_space hNX) _.
  have hLaws:=@LocalGerms.laws TX R (@analytic_representative_type R X NX hNX 0)
    (@analytic_representative_value R X NX hNX 0) 0.
  apply/(local_germ_equality hLaws).
  exists U;split.
  - exact:(@norm_class_zero_domain_open R X R^o NX (fun t=>`|t|) hNX U
      (analytic_representative_value w)
      (norm_class_continuous (norm_analytic_class_all_orders hw 0%N))).
  - split;first exact:haU.
    move=>x hx;rewrite hValuesF (hValuesW x hx) big_ord_recr /= /c eqxx.
    change ((\sum_(i<k) (xi x)^+i*analytic_representative_value (c i) (projection x))+
      (xi x)^+k*1 = (xi x)^+k+
        \sum_(i<k) (xi x)^+i*analytic_representative_value (a i) (projection x)).
    rewrite mulr1 addrC;congr (_+_);apply:eq_bigr=>i _.
    have hNe:((i:nat)==k) = false:=ltn_eqF (ltn_ord i).
    by rewrite /c hNe hD.
exists P;split;first exact:hDistinguished.
by rewrite hEval hGerms hW.
Qed.
End PreparedImage.
