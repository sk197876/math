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
  GenericRankSourceChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProductSource.
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

(** Source for [generic_rank_product_source_chart_exists]: choose convex
    V and W with g(U)=V times W in Federer 3.1.18, p. 229. The
    product is represented by its exact coordinate-box predicate inside
    R^(v+l), using the existing linear identification. *)
Theorem generic_rank_product_source_chart_exists (A:set X) (f:X->Y) (D:X->Hom X Y) a k :
  (1<=k)%N -> norm_class hNX hNY A f k ->
  is_norm_class_one_field NX NY A f D -> norm_generic_rank NX A D a v ->
  exists (p:{linear Y->V}) (j:{linear V->Y}) (beta:Hom X X)
    (g G:X->X) (U:set X) (e:R),
    is_linear_range_projection BY (D a) p j /\ 0<e /\ U a /\
    (forall x, U x -> A x /\ has_linear_rank (D x) v /\
      has_linear_rank (hom_comp (hom_of_linear p) (D x)) v) /\
    is_norm_diffeomorphism hNX hNX U (@euclidean_product_box R v l (g a) e) g G k /\
    (forall x, euclidean_first_block (g x)=p (f x)) /\
    g=norm_source_chart beta Ib (hom_of_linear p) (D a) f.
Proof.
move=>hk hf hD hgen.
have [p [j [beta [g [G [r [hP [hr [hO [hchart [hprefix hformula]]]]]]]]]]]:=
  @generic_rank_source_chart_exists R v l n A f D a k hk hf hD hgen.
pose O:=fun x=>NX (x-a)<r.
pose T:=g @` O.
have haO:O a by rewrite /O subrr inner_norm0.
have hgaT:T (g a):=@norm_diffeomorphism_maps R X X NX NX hNX hNX O T g G k hchart a haO.
have hGc:=@norm_diffeomorphism_inverse_class R X X NX NX hNX hNX O T g G k hchart.
have hG0:=@norm_class_continuous R X X NX NX hNX hNX T G k hGc.
have hT:=(@hG0 (g a) hgaT).1.
have [e [he hfit]]:=@euclidean_product_box_fits R v l T (g a) hT.
pose C:=@euclidean_product_box R v l (g a) e.
pose U:=fun x=>O x /\ C (g x).
have hsub:=@norm_diffeomorphism_target_restriction R X X NX NX hNX hNX O T C g G k
  hchart hfit (fun y hy=>@euclidean_product_box_open R v l (g a) e y hy).
exists p,j,beta,g,G,U,e; split=>//; split=>//; split.
- split; first exact haO.
  exact: euclidean_product_box_center he.
- split.
  + move=>x hx; exact: hO x hx.1.
  + split=>//; by split.
Qed.
End ProductSource.
