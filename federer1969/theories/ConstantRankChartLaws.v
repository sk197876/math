(** Federer (1969), 3.1.18, pp. 229–230: construction of the local
    source chart and preservation of both ranks before the fibre step.
    Source dimension is written v+l, covering every v<=m, including l=0.
    Complementary coordinates use the existing sealed linear chart;
    the target projection remains the printed orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormRegularity
  NormDiffeomorphismUP LinearRangeProjection NormSectionShear
  EuclideanBlockLinearMaps EuclideanProductBox ConstantRankChartUP
  NormDiffeomorphismClass LinearRangeProjectionLaws CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ConstantRankLaws.
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
Local Notation rb:=(@euclidean_first_block_map R v l).
Local Notation qb:=(@euclidean_last_block_map R v l).




(** Source for [constant_rank_chart_lower]: the same normal-form
    charts have each lower class, supporting the class-k convention of
    Federer 3.1.18, p. 229, from the class law of 3.1.11, p. 220. *)
Lemma constant_rank_chart_lower k t (A:set X) (f:X->Y) (D:X->Hom X Y) a
    (U:set X) e (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) (psi:V->Y) :
  (t<=k)%N -> is_euclidean_constant_rank_chart k A f D a U e p j g G psi ->
  is_euclidean_constant_rank_chart t A f D a U e p j g G psi.
Proof.
move=>ht [he ha hUA hP hs hp hcpsi hsec hf hformula hbase hdpsi htar hn hi hb hdh].
constructor=>//.
- exact: norm_diffeomorphism_lower ht hs.
- exact: norm_class_lower ht hcpsi.
- exact: norm_diffeomorphism_lower ht htar.
Qed.

(** Source for [constant_rank_flattened_image_in_range]: h[f(U)] lies
    in image Df(a), the containment in the penultimate paragraph of
    Federer 3.1.18, p. 230, from image h[f(U)]=p*(V). *)
Lemma constant_rank_flattened_image_in_range k (A:set X) (f:X->Y) (D:X->Hom X Y) a
    (U:set X) e (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) (psi:V->Y) :
  is_euclidean_constant_rank_chart k A f D a U e p j g G psi ->
  forall y, ((@norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi)
    @` (f @` U)) y -> exists x, D a x=y.
Proof.
move=>hC y hy.
rewrite (constant_rank_image hC) in hy.
have [u hu hju]:=hy.
apply: (range_projection_image (constant_rank_projection hC) y).1.
by exists u.
Qed.

(** Source for [constant_rank_projection_O_star]: p belongs to O*(n,v),
    the orthogonal-projection choice in Federer 3.1.18, p. 229. *)
Lemma constant_rank_projection_O_star k (A:set X) (f:X->Y) (D:X->Hom X Y) a
    (U:set X) e (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) (psi:V->Y) :
  is_euclidean_constant_rank_chart k A f D a U e p j g G psi -> @O_star R n v p.
Proof.
move=>hC; have hP:=constant_rank_projection hC.
exists j; split.
- exact: range_projection_orthogonal hP.
- exact: range_projection_adjoint hP.
Qed.
End ConstantRankLaws.
