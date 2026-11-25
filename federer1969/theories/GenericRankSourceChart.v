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
  EuclideanBlockLinearMaps NormSourceChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section GenericSource.
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

(** Source for [generic_rank_source_chart_exists]: the source chart
    g restricted to a neighbourhood U and its class-k inverse in
    Federer 3.1.18, p. 229, with the two equal ranks required on p. 230.
    The chosen beta is retained to support the same-chart smooth upgrade.
    This is the source half of the constant-rank theorem, not yet its
    final target normal form. *)
Theorem generic_rank_source_chart_exists (A:set X) (f:X->Y) (D:X->Hom X Y) a k :
  (1<=k)%N -> norm_class hNX hNY A f k ->
  is_norm_class_one_field NX NY A f D -> norm_generic_rank NX A D a v ->
  exists (p:{linear Y->V}) (j:{linear V->Y}) (beta:Hom X X)
    (g G:X->X) (r:R),
    is_linear_range_projection BY (D a) p j /\ 0<r /\
    (forall x, NX (x-a)<r -> A x /\ has_linear_rank (D x) v /\
      has_linear_rank (hom_comp (hom_of_linear p) (D x)) v) /\
    is_norm_diffeomorphism hNX hNX (fun x=>NX (x-a)<r)
      (g @` [set x|NX (x-a)<r]) g G k /\
    (forall x, euclidean_first_block (g x)=p (f x)) /\
    g=norm_source_chart beta Ib (hom_of_linear p) (D a) f.
Proof.
move=>hk hf hD hgen.
have [ha hrank]:=@norm_generic_rank_at_point R X Y NX hNX A D a v hgen.
have [p [j hP]]:=@linear_range_projection_exists R X Y BY hBY (D a) v hrank.
pose ph:=hom_of_linear p.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) ph.
have hs y:exists x, hom_comp ph (D a) x=y.
  exact (@range_projection_composition_surjective R X Y BY (D a) v p j hP y).
have ht:=@linear_surjective_rank_at_least R X V v (@coordinate_basis R v)
  (@coordinate_basisP R v) (hom_comp ph (D a)) hs.
have hDp:=@norm_class_one_linear_postcompose R X Y V NX NY NV hNX hNV A f D ph hD hp.
have hf0:=norm_class_one_zero hD.
have [s [hspos hPs]]:=@rank_threshold_interior R X V NX BX BV hBX hBV
  (v+l) (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) erefl
  A (fun x=>hom_comp ph (D x)) (fun x hx=>(@hf0 x hx).1)
  (norm_class_one_continuity hDp) a v ha ht.
have [t [htpos hGt]]:=hgen.
pose d:=Num.min s t.
have hd:0<d by rewrite /d lt_min hspos htpos.
pose O:=fun x=>NX (x-a)<d.
have hO x (hx:O x):A x /\ has_linear_rank (D x) v /\
    has_linear_rank (hom_comp ph (D x)) v.
  have hh:NX (x-a)<s /\ NX (x-a)<t.
    by move: hx; rewrite /O /d lt_min=>/andP.
  have hG:=hGt (x-a) hh.2; rewrite (addrC a (x-a)) subrK in hG.
  have hP':=hPs (x-a) hh.1; rewrite (addrC a (x-a)) subrK in hP'.
  split; first exact hG.1.
  split; first exact hG.2.
  exact (@linear_rank_from_full_threshold R X V v (@coordinate_basis R v)
    (@coordinate_basisP R v) (hom_comp ph (D x)) hP'.2).
have hopen x (hx:O x):norm_domain_interior NX O x.
  exact (@norm_open_ball_domain_interior R X NX hNX a d x hx).
have hOA x (hx:O x):A x:=(hO x hx).1.
have hfO:=@norm_class_open_restriction R X Y NX NY hNX hNY A O f k hOA hopen hf.
have hDO:=@norm_class_one_field_open_restriction R X Y NX NY A O f D hOA hopen hD.
have [beta [gamma [hbg [hgb hprefix]]]]:=@euclidean_epimorphism_block_chart_exists R v l
  (hom_as_linear (hom_comp ph (D a))) hs.
have hbeta:=@norm_finite_linear_bounded R X X NX NX hNX hNX (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) beta.
have hI:=@norm_finite_linear_bounded R V X NV NX hNV hNX v
  (@coordinate_basis R v) (@coordinate_basisP R v) Ib.
have hL:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) (D a).
pose g:=norm_source_chart beta Ib ph (D a) f.
have hgc:=@norm_source_chart_class R X Y V NX NY NV hNX hNY hNV O beta Ib ph
  (D a) f k hbeta hI hp hL hfO.
have haO:O a by rewrite /O subrr inner_norm0.
have hgd:=@norm_source_chart_differential R X Y V NX NY NV hNX hNY hNV O beta Ib ph
  (D a) f a hbeta hI hp (norm_class_one_differential hDO haO).
have hgc1:=@norm_class_lower R X X NX NX hNX hNX O g k 1%N hk hgc.
have [DG hDG]:=(@norm_class_firstP R X X NX NX hNX hNX O g).1 hgc1.
have heq:=norm_differential_unique hNX hNX (norm_class_one_differential hDG haO) hgd.
have hinj:injective (DG a).
  rewrite heq; exact: can_inj hbg.
have [r [hr [hOr [G hchart]]]]:=@finite_local_diffeomorphism R X BX hBX hNX
  (v+l) (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) O g DG a k
  hgc hDG haO hinj.
exists p,j,beta,g,G,r; split=>//; split=>//; split.
- move=>x hx; exact: hO x (hOr x hx).
- split=>//; split; last by [].
  move=>x.
  exact (@norm_source_chart_prefix R X Y V beta Ib ph (D a)
    (@euclidean_first_block_map R v l) f (@euclidean_first_block_injectionK R v l)
    hprefix x).
Qed.
End GenericSource.
