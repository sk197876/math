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

Section ConstantRankTheorem.
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


(** Source for [federer_3_1_18]: the local constant-rank theorem in
    Federer 3.1.18, pp. 229–230, including both diffeomorphisms, the
    exact image p*(V), the factorisation and Dh[f(a)]=identity.
    Writing m=v+l covers every admissible rank; l=0 is the printed
    full-source-rank case. D is the actual differential field, not an
    additional chosen approximation hypothesis. *)
Theorem federer_3_1_18 (A:set X) (f:X->Y) (D:X->Hom X Y) a k :
  (1<=k)%N -> norm_class hNX hNY A f k ->
  is_norm_class_one_field NX NY A f D -> norm_generic_rank NX A D a v ->
  exists (U:set X) (e:R) (p:{linear Y->V}) (j:{linear V->Y})
    (g G:X->X) (psi:V->Y),
    @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi.
Proof.
move=>hk hf hD hgen.
have [p [j [beta [g [G [U [e [hP [he [haU [hU [hchart [hprefix hformula]]]]]]]]]]]]]:=
  @generic_rank_product_source_chart_exists R v l n A f D a k hk hf hD hgen.
exists U,e,p,j,g,G,(fun u=>f (G (Ib u+@euclidean_last_injection_map R v l
  (@euclidean_last_block_map R v l (g a))))).
exact (@constant_rank_chart_from_product_source R v l n A U f D a k p j g G e
  hk hf hD hP he haU hU hchart (fun x _=>hprefix x)).
Qed.
End ConstantRankTheorem.

(** Source for [generic_rank_dimension_bounds]: v<=inf{m,n},
    stated in Federer 3.1.18, p. 229. The statement includes every
    finite source and target dimension and every nonnegative rank. *)
Theorem generic_rank_dimension_bounds (R:realType) m n v
    (A:set (R_n R m)) (D:R_n R m->Hom (R_n R m) (R_n R n)) a :
  norm_generic_rank (inner_norm (@euclidean_inner_productP R m)) A D a v ->
  (v<=minn m n)%N.
Proof.
move=>hgen.
have [_ hRank]:=@norm_generic_rank_at_point R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) A D a v hgen.
rewrite leq_min; apply/andP; split.
- exact (@linear_rank_domain_bound R (R_n R m) (R_n R n) (D a) m
    (@coordinate_basis R m) (@coordinate_basisP R m) v hRank).
- exact (@linear_rank_codomain_bound R (R_n R m) (R_n R n) (D a) n
    (@coordinate_basis R n) (@coordinate_basisP R n) v hRank).
Qed.

(** Source for [federer_3_1_18_zero]: the rank-zero conclusion in
    Federer 3.1.18, p. 229: a neighbourhood is mapped onto {f(a)}.
    The result includes zero source or target dimensions. *)
Theorem federer_3_1_18_zero (R:realType) m n (A:set (R_n R m))
    (f:R_n R m->R_n R n) (D:R_n R m->Hom (R_n R m) (R_n R n)) a :
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  norm_generic_rank (inner_norm (@euclidean_inner_productP R m)) A D a 0%N ->
  exists r:R, 0<r /\ forall x, inner_norm (@euclidean_inner_productP R m) (x-a)<r ->
    A x /\ f x=f a.
Proof.
move=>hD hgen.
exact (@norm_generic_rank_zero_locally_constant R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) A f D a
  (fun x hx=>norm_class_one_differential hD hx) hgen).
Qed.
