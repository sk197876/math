(** Federer (1969), 3.4.4, pp. 317–318: the
    original Cantor and Whitney examples prove sharpness in every dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity ContinuousMultilinearUP ContinuousMultilinearSealed
  PowerCantorPairUP PowerCantorPair RealMetricBackground EuclideanOneCoordinate
  BinaryCantorFlatExtension FirstZeroFormDifferential CriticalSharpnessParameters
  CriticalSharpnessParameterLaws CriticalSharpProductUP CriticalSharpProductClass
  CriticalSharpProductRank CriticalSharpProductImage CriticalPrefixRank
  CriticalSharpProductPositiveMass RealHausdorffMeasure InnerOwnNormRealHausdorff LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_4_4]: the complete sharpness
    construction in 3.4.4, pp. 317–318. For
    every positive degree gamma below nu+(m-nu)/k,
    construct a whole-space map of class k and its original
    Cantor coordinate source B. Its actual differential has
    rank exactly nu on B, and its original image has
    positive Gamma-normalized measure at a degree strictly
    above gamma. The original correspondence, sharp Holder
    coefficient, flat Whitney extension, coordinate formulas,
    and real-degree product positivity are all proved earlier;
    no sharpness, image, or rank conclusion is assumed. *)
Theorem federer_3_4_4 (R:realType) m nu k (gamma:R):
  (nu<m)%N ->(1<=k)%N ->(0<gamma)%R ->
  (gamma<nu%:R+(m-nu)%:R/k%:R)%R ->
  exists s:R,exists hs:(0<=s)%R,
  exists B:set (R_n R m),exists f:R_n R m->R_n R m,
    (gamma<s)%R /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True) f k /\
    (forall x,B x ->exists D:Hom (R_n R m) (R_n R m),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) f x D /\
      has_linear_rank D nu) /\
    (0<@real_hausdorff_measure R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      s hs (f @` B))%E.
Proof.
move=>hNu hK hGamma hGammaUpper.
have [beta [alpha [hBeta [hBetaUpper [hBetaK [hAlpha [hAlphaUpper [hBetaAlpha hImageDegree]]]]]]]]:=
  @critical_sharpness_parameters R m nu k gamma hNu hK hGamma hGammaUpper.
have hOrder:(k%:R<alpha/beta)%R:=critical_sharpness_holder_exponent hK hBeta hBetaAlpha.
have hTwo (j:nat):(2<=2)%N:=leqnn 2.
have [A [u hPairA]]:=@power_cantor_pair_exists R 1 alpha (fun _:nat=>2%N)
  ltr01 hAlpha hAlphaUpper hTwo.
have [C [v hPairC]]:=@power_cantor_pair_exists R 1 beta (fun _:nat=>2%N)
  ltr01 hBeta hBetaUpper hTwo.
have [g [hG [hGImage hFlat]]]:=@binary_cantor_flat_extension_exists R alpha beta k A C u v
  hAlpha hAlphaUpper hBeta hBetaUpper hOrder hPairA hPairC.
have [F hF]:=@critical_sharp_product_map_exists R m nu g.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose N1:=inner_norm (@euclidean_inner_productP R 1).
pose hN1:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose NS:=fun t:R^o=>(`|t|)%R.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i (R_n R 1) R^o N1 NS hN1 hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i (R_n R 1) R^o N1 NS hN1 hNS.
pose ZN i:=@ContinuousMultilinear.norm R i (R_n R 1) R^o N1 NS hN1 hNS.
have hZ i:is_continuous_multilinear_space N1 NS (@ev i) (@ZN i).
  exact:ContinuousMultilinear.laws.
have hGZero a:A a ->has_norm_differential N1 NS (fun _=>True) g (euclidean_one_embed a) 0%R.
  move=>ha.
  have hRange:(1<=1<=k)%N by apply/andP;split.
  exact:(@first_zero_form_is_zero_differential R (R_n R 1) R^o N1 NS hN1 hNS
    Z ev ZN hZ (fun _=>True) g (euclidean_one_embed a) (@hFlat a ha 1%N hRange)).
have hClass:=@critical_sharp_product_map_class R m nu g F k hF hG.
have hFirst:norm_class_one N N (fun _=>True) F.
  exact:(norm_class_firstP hN hN (fun _=>True) F).1 (norm_class_lower hK hClass).
pose B:=@critical_sharp_product_source R m nu A.
have hRank x (hx:B x):has_norm_differential N N (fun _=>True) F x
    (@critical_prefix_linear_map R m nu) /\has_linear_rank (@critical_prefix_linear_map R m nu) nu.
  apply:(@critical_sharp_product_rank R m nu g F x (ltnW hNu) hF hFirst).
  move=>i hi;exact:hGZero (x i) (hx i hi).
pose s:=(nu%:R+(m-nu)%:R*beta)%R.
have hs:(0<=s)%R:=ltW (lt_trans hGamma hImageDegree).
have hImage:=@critical_sharp_product_exact_image R m nu g F A C hF hGImage.
have hPositive:=@critical_sharp_product_positive_hausdorff R m nu beta (fun _:nat=>2%N)
  C v hs (ltnW hNu) hBeta hBetaUpper hPairC.
exists s,hs,B,F;split;first exact:hImageDegree.
split;first exact:hClass.
split.
- move=>x hx;exists (@critical_prefix_linear_map R m nu);exact:hRank x hx.
- rewrite (@inner_own_norm_real_hausdorff R X (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) s hs (F @` B)).
  by rewrite /B hImage.
Qed.
