(** Federer (1969), 3.2.31, p. 269: a small coefficient
    in every exterior basis word bounds the actual exterior
    norm of the approximating symmetric automorphism. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerProductLaws Bilinear InnerNorm InnerNormalization
  OrthonormalFamilies LinearBasis SimpleAdaptedBasis FiniteExteriorPowers ExteriorIndices LambdaPermutation
  ExteriorGrading ExteriorNorm ExteriorOperatorNorm ExteriorBasisWedgeNorm ExteriorHadamardEquality
  SingleFactorProductBound OrthogonalExteriorBasisBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [diagonal_exterior_small_factor_bound]: supporting
    norm(Lambda^mu t)<epsilon in Federer 3.2.31, p. 269.
    For an actual diagonal map in an orthonormal basis, all
    coefficients lie between zero and M, and each mu-word
    has a distinguished coefficient at most d. The existing
    single-factor product bound and the actual orthogonal
    exterior-basis norm calculation give d*M^(mu-1).
    A distinguished factor is proved for each word; no empty
    product is treated as having a small factor. *)
Theorem diagonal_exterior_small_factor_bound (R:realType)
    (h2:(1+1:R)!=0) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) (hE:orthonormal_family B e)
    (f:{linear V->V}) (c:'I_n->R) mu (d M:R):
  0<=d ->0<=M ->(forall i,0<=c i) ->(forall i,c i<=M) ->
  (forall i,f (e i)=c i*:e i) ->
  (forall lambda:Lambda n mu,exists j:'I_mu,c (tnth (val lambda) j)<=d) ->
  exterior_operator_norm h2 hB hB he f mu<=d*M^+mu.-1.
Proof.
move=>hd hM hC hCM hMap hSmall.
have hOrth i j:i!=j ->B (f (e i)) (f (e j))=0.
  move=>hij; rewrite !hMap (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)) hE (negbTE hij).
  change (c i*(c j*0)=0); by rewrite !mulr0.
have hNorm i:inner_norm hB (f (e i))=c i.
  by rewrite hMap inner_normZ (ger0_norm (hC i)) (orthonormal_norm1 hB hE) mulr1.
have hWords (lambda:Lambda n mu):
    exterior_norm h2 hB (e_lambda (fun i=>f (e i)) (val lambda))<=d*M^+mu.-1.
  have hSel i j:i!=j ->B (f (e (tnth (val lambda) i))) (f (e (tnth (val lambda) j)))=0.
    move=>hij; apply:hOrth; by rewrite (inj_eq (@Lambda_tnth_injective n mu lambda)).
  rewrite indexed_productE (orthogonal_product_norm h2 hB hSel).
  under eq_bigr do rewrite hNorm.
  have [j hj]:=hSmall lambda.
  have hh:=@single_factor_product_bound R [the finType of 'I_mu]
    (fun i=>c (tnth (val lambda) i)) j d M hd hM
    (fun i=>hC (tnth (val lambda) i)) hj (fun i _=>hCM (tnth (val lambda) i)).
  by rewrite card_ord in hh.
exact (@orthogonal_exterior_basis_operator_bound R h2 V V B B hB hB n e he hE f mu
  (d*M^+mu.-1) (mulr_ge0 hd (exprn_ge0 mu.-1 hM)) hOrth hWords).
Qed.
