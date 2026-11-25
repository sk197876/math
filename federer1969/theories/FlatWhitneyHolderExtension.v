(** Federer (1969), 3.4.4, p. 318: apply
    the proved Whitney theorem to the actual constant jets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms SymmetricFormZero
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormClassHigherUP NormRegularity NormHigherSymmetricFormUP WhitneyModulusUP WhitneyExtension
  FlatWhitneyPolynomial FlatWhitneyHolderJets RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Extension.
Variable R:realType.
Variable m:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i (R_n R m) Y N NY hN hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i (R_n R m) Y N NY hN hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i (R_n R m) Y N NY hN hNY).

(** Source for [flat_whitney_holder_extension_exists]: the
    map g of class k whose values are phi and whose
    positive derivatives through order k vanish on the original
    closed source, 3.4.4, p. 318. Derive every
    Whitney hypothesis from the actual Holder estimate, then
    use 3.1.14 through its public theorem. Every selected
    jet and extension remains a local existence witness. *)
Theorem flat_whitney_holder_extension_exists (A:set X) (phi:X->Y) k (C p:R):
  closed A ->0<C ->k%:R<p ->
  (forall a b,A a ->A b ->NY (phi a-phi b)<=C*real_power (N (a-b)) p) ->
  exists g:X->Y,norm_class hN hNY (fun _=>True) g k /\
    (forall a,A a ->g a=phi a) /\
    forall a,A a ->forall i,(1<=i<=k)%N ->
      is_norm_higher_differential_form N ev ZN (fun _=>True) g i a 0.
Proof.
move=>hA hC hP hHolder.
have hEach a:=@flat_whitney_constant_polynomial_exists R (R_n R m) Y (phi a).
have [P hPolynomial]:=choice hEach.
have hZero a x:polynomial_taylor_coefficient (P a) 0 x=zero_sform (R_n R m) (phi a).
  exact:(hPolynomial a).2.2.1 x.
have hPositive a i x:polynomial_taylor_coefficient (P a) i.+1 x=0.
  exact:(hPolynomial a).2.2.2 i x.
have hDegree a:polynomial_degree (P a)=0%N:= (hPolynomial a).2.1.
have hJets:is_whitney_jet_family NY k P A.
  exact:(@flat_whitney_holder_jet_family R m Y NY hNY P phi hZero hPositive
    A k C p hA hC hP hDegree hHolder).
have hZ i:is_continuous_multilinear_space N NY (@ev i) (@ZN i).
  exact:ContinuousMultilinear.laws.
have [g [hG hForms]]:=@federer_3_1_14 R m Y NY hNY Z ev ZN hZ k A P hJets.
exists g;split=>//;split.
- move=>a ha.
  have [z [hz hEvaluation]]:=hForms a ha 0%N (leq0n k).
  have hValue:=hEvaluation [ffun i:'I_0=>(0:X)].
  rewrite hZero zero_sformE in hValue.
  exact:eq_trans (esym hz.2) hValue.
- move=>a ha [|i] /andP[hi hik];first by [].
  have hForm:=hForms a ha i.+1 hik.
  by rewrite hPositive in hForm.
Qed.
End Extension.
