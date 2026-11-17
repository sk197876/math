(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    polynomial supplied by preparation belongs to the original
    transverse polynomial subring. Its actual coefficients are
    monic and vanish at the transverse origin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormMetric NormAnalyticUP NormRegularity
  NormClassZeroTopology NormAnalyticLocal LocalGermUP LocalGermSealed HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermValueUP HolomorphicGermValueSealed
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback ComplexWeierstrassPreparationUP
  WeierstrassFiniteFamilyExtension HolomorphicTransversePolynomialRepresentative
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
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Hypothesis hXiValues:forall x,holomorphic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Local Notation value:=(@HolomorphicGermValue.map R K NK (complex_norm_real hNK) (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [holomorphic_prepared_polynomial_image]: the
    original prepared W is the image of a monic
    distinguished polynomial in the transverse germ ring,
    expanding the subring assertion of 3.4.7, p. 325.
    The representatives are those of preparation, and their
    neighbourhood equation proves the identification. *)
Theorem holomorphic_prepared_polynomial_image k (W:G)
    (Wi:'I_k->@holomorphic_germ_ring R K NK (complex_norm_real hNK) 0):
  @is_complex_weierstrass_polynomial_germ R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) xi projection k W Wi ->
  exists P:B,is_distinguished_polynomial coefficient value P k /\J P = W.
Proof.
move=>[w [hW [a [hA [hZero [U [haU [hw hValuesW]]]]]]]].
have hHolomorphic i:exists V:set K,V (projection 0) /\
    is_holomorphic (complex_norm_real hNK) (@complex_modulus_real_norm R) V
      (holomorphic_representative_value (a i)).
  rewrite (linear0 projection);exact:holomorphic_representative_holomorphic (a i).
pose converted i:@holomorphic_representative_type R K NK (complex_norm_real hNK) (projection 0):=
  exist _ (holomorphic_representative_value (a i)) (hHolomorphic i).
pose oneRep:=@holomorphic_constant_representative R K NK (complex_norm_real hNK) (projection 0) 1.
have [d hD]:=@weierstrass_finite_family_extension
  (@holomorphic_representative_type R K NK (complex_norm_real hNK) (projection 0)) k converted oneRep.
pose c i:=if i==k then oneRep else d i.
pose P:=\sum_(i<k.+1) embed (holomorphic_germ (c i))*variable^+i.
have hCoefficient i:coefficient P i = if (i<k.+1)%N then (holomorphic_germ (c i):A) else 0.
  exact:(@polynomial_finite_expression_coefficient A B embed variable coefficient hP
    k.+1 (fun i=>holomorphic_germ (c i)) i).
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
    rewrite hCoefficient hBound /c hNe (@HolomorphicGermValue.laws R K NK (complex_norm_real hNK) (projection 0)).
    have hDi:=hD (Ordinal hi).
    change (d i=converted (Ordinal hi)) in hDi.
    rewrite hDi /converted /holomorphic_representative_value /= (linear0 projection).
    exact:hZero.
have [f [hValuesF hGermF]]:=@holomorphic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k.+1 c hXiValues.
have hEval:J P = holomorphic_germ f.
  rewrite hGermF (@polynomial_evaluation_finite_expression A B G embed variable coefficient
    hP E Gamma J hJ P k.+1 hSupport).
  apply:eq_bigr=>i _;by rewrite hCoefficient (ltn_ord i).
have hGerms:holomorphic_germ f=holomorphic_germ w.
  pose TX:=Topological.clone (real_norm_metric_space (complex_norm_real hNX)) _.
  have hLaws:=@LocalGerms.laws TX (ComplexScalars.C R) (@holomorphic_representative_type R X NX (complex_norm_real hNX) 0)
    (@holomorphic_representative_value R X NX (complex_norm_real hNX) 0) 0.
  apply/(local_germ_equality hLaws).
  exists U;split.
  - exact:(@norm_class_zero_domain_open R (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) U
      (holomorphic_representative_value w)
      (norm_class_continuous (norm_analytic_class_all_orders hw.1 0%N))).
  - split;first exact:haU.
    move=>x hx;rewrite hValuesF (hValuesW x hx) big_ord_recr /= /c eqxx.
    change ((\sum_(i<k) (xi x)^+i*holomorphic_representative_value (c i) (projection x))+
      (xi x)^+k*1 = (xi x)^+k+
        \sum_(i<k) (xi x)^+i*holomorphic_representative_value (a i) (projection x)).
    rewrite mulr1 addrC;congr (_+_);apply:eq_bigr=>i _.
    have hNe:((i:nat)==k) = false:=ltn_eqF (ltn_ord i).
    by rewrite /c hNe hD.
exists P;split;first exact:hDistinguished.
by rewrite hEval hGerms hW.
Qed.
End PreparedImage.
