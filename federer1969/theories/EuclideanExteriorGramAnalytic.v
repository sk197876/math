(** Federer (1969), 3.2.33, p. 270: the actual
    Hilbert exterior Gram rank functions are analytic.
    The orthonormal-sum formula of 1.7.9 and permutation
    formula of 1.7.5 reduce them to scalar polynomials. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  fingroup perm.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanStiefelInnerSplitting EuclideanHomOperator
  InnerNorm RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticOperations
  NormAnalyticConstant NormAnalyticScalarProducts EuclideanOperatorCoordinateAnalytic
  InnerProductUP InnerExterior InnerExteriorPositivity InnerExteriorProducts InnerExteriorBasis
  ExteriorGrading ExteriorMaps ExteriorMapNormContinuity FiniteExteriorPowers FiniteOrdinalBasis ExteriorIndices
  HomInner HomInnerCoordinates InversionCount OrthonormalFamilies LinearRankExterior EuclideanExteriorGramRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AnalyticGram.
Variable R:realType.
Variables m n q:nat.
Local Notation H:=(Hom (R_n R m) (R_n R n)).
Local Notation N:=(@euclidean_operator_norm R m n).
Local Notation hN:=(@euclidean_operator_norm_is_norm R m n).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation AN f:=(@norm_analytic R H R^o N NS hN hNS setT f).

(** Source for [euclidean_operator_vector_pairing_analytic]:
    the scalar products entering the permutation formula for
    h_i, Federer 3.2.33, p. 270, expanded using
    1.7.1, p. 28. Both vector evaluations are actual
    values of the original linear map. *)
Lemma euclidean_operator_vector_pairing_analytic (v w:R_n R m):
  AN (fun L=>euclidean_inner_product (L v) (L w)).
Proof.
apply:(@norm_analytic_finite_scalar_sum R H N hN setT (Finite.clone 'I_n _)
  (fun i L=>(L v) i*(L w) i)).
- move=>L _; exists 1; split; first exact:ltr01; by move=>M hM.
- move=>i; apply:norm_analytic_scalar_product;
    exact:euclidean_operator_coordinate_analytic.
Qed.

(** Source for [euclidean_exterior_word_gram_analytic]: the
    squared Hilbert length of one actual exterior image is
    analytic in its linear map, supporting the displayed h_i
    in Federer 3.2.33, p. 270. The permutation
    expansion includes the empty product in exterior degree zero. *)
Lemma euclidean_exterior_word_gram_analytic (e:'I_q->R_n R m):
  AN (fun L=>@exterior_inner_form R (euclidean_two_nonzero R)
    (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) q
    (e_lambda (fun i=>L (e i)) (ord_tuple q))
    (e_lambda (fun i=>L (e i)) (ord_tuple q))).
Proof.
have hOpen L (_:setT L):norm_domain_interior N setT L.
  exists 1; split; first exact:ltr01; by move=>M hM.
have hPolynomial:AN (fun L=>\sum_(s:'S_q) FedererPermutation.index R s*
    \prod_(i:'I_q) euclidean_inner_product (L (e (s i))) (L (e i))).
  apply:norm_analytic_finite_scalar_sum=>//s.
  apply:norm_analytic_scalar_product.
  - exact:(@norm_constant_analytic R H R^o N NS hN hNS setT hOpen
      (FedererPermutation.index R s)).
  - apply:norm_analytic_finite_scalar_product=>//i.
    exact:euclidean_operator_vector_pairing_analytic.
apply:(@norm_analytic_domain_agreement R H R^o N NS hN hNS setT
  (fun L=>\sum_(s:'S_q) FedererPermutation.index R s*
    \prod_(i:'I_q) euclidean_inner_product (L (e (s i))) (L (e i))) _ _ hPolynomial).
move=>L _; rewrite exterior_inner_product_permutations.
apply:eq_bigr=>s _; congr (_*_).
by rewrite foldrE big_map enumT.
Qed.

(** Source for [euclidean_exterior_gram_analytic]: analyticity
    of exactly h_i=exterior_i(Df) dot exterior_i(Df),
    Federer 3.2.33, p. 270. The actual Hilbert Hom
    inner square is a finite sum over the orthonormal
    exterior coordinate basis, by 1.7.9, p. 35.
    This preserves all natural degrees and zero spaces. *)
Theorem euclidean_exterior_gram_analytic:
  AN (@euclidean_exterior_gram R m n q).
Proof.
pose e:=fun i:'I_#|{:Lambda m q}|=>
  @finite_e_lambda R m (R_n R m) (@coordinate_basis R m) q (enum_val i).
pose hb:=finite_ordinal_basis (@finite_e_lambda_basis R m (R_n R m)
  (@coordinate_basis R m) (@coordinate_basisP R m) (euclidean_two_nonzero R) q).
have ho:orthonormal_family
    (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R m)
      (@euclidean_inner_product R m) (@euclidean_inner_productP R m) q) e.
  move=>i j; rewrite /e /finite_e_lambda.
  rewrite (@exterior_orthonormal_family R (euclidean_two_nonzero R)
    (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m)
    m (@coordinate_basis R m) (@euclidean_coordinate_orthonormal_family R m) q).
  by rewrite (inj_eq enum_val_inj).
have hPolynomial:AN (fun L=>\sum_(i:'I_#|{:Lambda m q}|)
    @exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) q
      (e_lambda (fun j=>L (@coordinate_basis R m
        (tnth (val (enum_val i:Lambda m q)) j))) (ord_tuple q))
      (e_lambda (fun j=>L (@coordinate_basis R m
        (tnth (val (enum_val i:Lambda m q)) j))) (ord_tuple q))).
  apply:norm_analytic_finite_scalar_sum.
  - move=>L _; exists 1; split; first exact:ltr01; by move=>M hM.
  - move=>i; exact:euclidean_exterior_word_gram_analytic.
apply:(@norm_analytic_domain_agreement R H R^o N NS hN hNS setT _
  (@euclidean_exterior_gram R m n q) _ hPolynomial).
move=>L _; rewrite /euclidean_exterior_gram
  (hom_inner_orthonormal_sum _ _ hb hb ho).
apply:eq_bigr=>i _.
have hWord:exterior_power_map (hom_as_linear L) q (e i)=
    e_lambda (fun j=>L (@coordinate_basis R m
      (tnth (val (enum_val i:Lambda m q)) j))) (ord_tuple q).
  rewrite /e /finite_e_lambda exterior_power_map_e_lambda.
  exact:exterior_product_tuple_reindex.
by rewrite hWord.
Qed.
End AnalyticGram.
