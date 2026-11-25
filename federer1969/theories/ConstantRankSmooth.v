(** Federer (1969), 3.1.18, pp. 229–230: construction of the local
    source chart and preservation of both ranks before the fibre step.
    Source dimension is written v+l, covering every v<=m, including l=0.
    Complementary coordinates use the existing sealed linear chart;
    the target projection remains the printed orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates InnerProductUP InnerNorm HilbertFormCompactness
  RealNormUP NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  NormRegularity NormRegularityOperations NormOpenDomainLaws
  NormClassOneRestriction NormClassOneLinearPostcompose NormFiniteLinearBound
  NormDiffeomorphismUP FiniteLocalDiffeomorphism NormRankZero LinearRankUP
  LinearRankAtLeast RankThresholdOpen LinearSurjectiveRank
  LinearRangeProjection LinearRangeProjectionLaws EuclideanEpimorphismBlockChart
  EuclideanBlockLinearMaps NormSourceChart EuclideanProductBox NormDiffeomorphismRestriction
  GenericRankSourceChart GenericRankProductSourceChart ConstantRankChartUP
  ConstantRankChartAssembly ConstantRankChartLaws NormDiffeomorphismClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothConstantRank.
Variable R:realType.
Variables v l n:nat.
Local Notation X:=(R_n R (v+l)).
Local Notation Y:=(R_n R n).
Local Notation V:=(R_n R v).
Local Notation BX:=(@euclidean_inner_product R (v+l)).
Local Notation BY:=(@euclidean_inner_product R n).
Local Notation BV:=(@euclidean_inner_product R v).
Local Notation hBX:=(@euclidean_inner_productP R (v+l)).
Local Notation hBY:=(@euclidean_inner_productP R n).
Local Notation hBV:=(@euclidean_inner_productP R v).
Local Notation NX:=(inner_norm hBX).
Local Notation NY:=(inner_norm hBY).
Local Notation NV:=(inner_norm hBV).
Local Notation hNX:=(inner_norm_real_norm hBX).
Local Notation hNY:=(inner_norm_real_norm hBY).
Local Notation hNV:=(inner_norm_real_norm hBV).
Local Notation Ib:=(@euclidean_first_injection_map R v l).
Local Notation Jb:=(@euclidean_last_injection_map R v l).
Local Notation qb:=(@euclidean_last_block_map R v l).



(** Source for [federer_3_1_18_smooth]: the class-infinity instance
    of the normal form in Federer 3.1.18, pp. 229–230, using the class
    convention of 3.1.11, p. 220. The same U,V,W,p,g,h and inverses
    satisfy every finite class, rather than being chosen independently
    for each derivative order. *)
Theorem federer_3_1_18_smooth (A:set X) (f:X->Y) (D:X->Hom X Y) a :
  norm_class_all_orders hNX hNY A f ->
  is_norm_class_one_field NX NY A f D -> norm_generic_rank NX A D a v ->
  exists (U:set X) (e:R) (p:{linear Y->V}) (j:{linear V->Y})
    (g G:X->X) (psi:V->Y), forall k,
    @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi.
Proof.
move=>hf hD hgen.
have hk1:(1<=1)%N by [].
have [p [j [beta [g [G [U [e [hP [he [haU [hU [hchart [hprefix hformula]]]]]]]]]]]]]:=
  @generic_rank_product_source_chart_exists R v l n A f D a 1%N hk1 (@hf 1%N) hD hgen.
pose C:=@euclidean_product_box R v l (g a) e.
pose ph:=hom_of_linear p.
pose psi:=fun u:V=>f (G (Ib u+Jb (qb (g a)))).
have hgc1:=@norm_diffeomorphism_forward_class R X X NX NX hNX hNX U C g G 1%N hchart.
have hGc1:=@norm_diffeomorphism_inverse_class R X X NX NX hNX hNX U C g G 1%N hchart.
have hg0:=@norm_class_continuous R X X NX NX hNX hNX U g 1%N hgc1.
have hopen x (hx:U x):norm_domain_interior NX U x:=(@hg0 x hx).1.
have hUA x (hx:U x):A x:=(hU x hx).1.
have hgC x (hx:U x):C (g x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX U C g G 1%N hchart x hx.
have hGU z (hz:C z):U (G z):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U C g G 1%N hchart z hz.
have hgG z (hz:C z):g (G z)=z:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U C g G 1%N hchart z hz.
have hGg x (hx:U x):G (g x)=x:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX U C g G 1%N hchart x hx.
have hb:=@norm_finite_linear_bounded R X X NX NX hNX hNX (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) beta.
have hi:=@norm_finite_linear_bounded R V X NV NX hNV hNX v
  (@coordinate_basis R v) (@coordinate_basisP R v) Ib.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) ph.
have hL:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) (D a).
have hpositive k (hk:(1<=k)%N):@is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi.
  have hfU:=@norm_class_open_restriction R X Y NX NY hNX hNY A U f k hUA hopen (@hf k).
  have hgk:norm_class hNX hNX U g k.
    rewrite hformula.
    exact (@norm_source_chart_class R X Y V NX NY NV hNX hNY hNV U beta Ib ph (D a)
      f k hb hi hp hL hfU).
  have hGk:=@norm_class_inverse_from_first R X X NX NX hNX hNX U C g G k
    hgC hGU hGg hgG hgk hGc1.
  have hchartk:is_norm_diffeomorphism hNX hNX U C g G k.
    constructor=>//.
    exact: norm_diffeomorphism_spaces hchart.
  exact (@constant_rank_chart_from_product_source R v l n A U f D a k p j g G e
    hk (@hf k) hD hP he haU hU hchartk (fun x _=>hprefix x)).
exists U,e,p,j,g,G,psi.
move=>[|k].
- exact (@constant_rank_chart_lower R v l n 1%N 0%N A f D a U e p j g G psi
    (leq0n 1%N) (hpositive 1%N hk1)).
- have hk:(1<=k.+1)%N by [].
  exact: hpositive k.+1 hk.
Qed.
End SmoothConstantRank.
