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
  ConstantRankChartAssembly ConstantRankChartLaws NormDiffeomorphismClass
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormAnalyticLinear NormAnalyticConstant
  NormAnalyticInverse AnalyticCoordinateMaps NormSectionShearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AnalyticConstantRank.
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



(** Source for [is_euclidean_analytic_constant_rank_chart]: the
    analytic analogue of every coordinate map in 3.1.18, asserted
    in Federer 3.1.24, p. 240. The original class-one chart laws
    retain all geometry and derivatives; each displayed coordinate
    map and its inverse is additionally required to be analytic. *)
Definition is_euclidean_analytic_constant_rank_chart (A:set X) (f:X->Y) (D:X->Hom X Y) a
    (U:set X) e (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) (psi:V->Y) :=
  @is_euclidean_constant_rank_chart R v l n 1%N A f D a U e p j g G psi /\
  @norm_analytic R X X NX NX hNX hNX U g /\
  @norm_analytic R X X NX NX hNX hNX (@euclidean_product_box R v l (g a) e) G /\
  @norm_analytic R V Y NV NY hNV hNY (constant_rank_parameter_domain g a e) psi /\
  @norm_analytic R Y Y NY NY hNY hNY (constant_rank_target_domain g a e p)
    (@norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi) /\
  @norm_analytic R Y Y NY NY hNY hNY (constant_rank_target_domain g a e p)
    (@norm_section_shear_inverse R Y V (hom_of_linear p) (hom_of_linear j) psi).

(** Source for [federer_3_1_18_analytic]: the analytic constant-rank
    normal form, Federer 3.1.24, p. 240, referring to 3.1.18,
    pp. 229–230. Use the printed explicit source change, prove it
    analytic by arithmetic, apply the proved analytic inverse theorem,
    then obtain the section by an affine slice and the target shears
    by their displayed formulas. Smoothness alone is never used to
    infer analyticity. All dimension boundaries are retained. *)
Theorem federer_3_1_18_analytic (A:set X) (f:X->Y) (D:X->Hom X Y) a :
  @norm_analytic R X Y NX NY hNX hNY A f ->
  is_norm_class_one_field NX NY A f D -> norm_generic_rank NX A D a v ->
  exists (U:set X) (e:R) (p:{linear Y->V}) (j:{linear V->Y})
    (g G:X->X) (psi:V->Y), is_euclidean_analytic_constant_rank_chart A f D a U e p j g G psi.
Proof.
move=>hfA hD hgen.
have hf:=norm_analytic_class_all_orders hfA.
have hk1:(1<=1)%N by [].
have [p [j [beta [g [G [U [e [hP [he [haU [hU [hchart [hprefix hformula]]]]]]]]]]]]]:=
  @generic_rank_product_source_chart_exists R v l n A f D a 1%N hk1 (@hf 1%N) hD hgen.
pose C:=@euclidean_product_box R v l (g a) e.
pose ph:=hom_of_linear p.
pose psi:=fun u:V=>f (G (Ib u+Jb (qb (g a)))).
have hg0:=@norm_class_continuous R X X NX NX hNX hNX U g 1%N
  (norm_diffeomorphism_forward_class hchart).
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
have hj:=@norm_finite_linear_bounded R V Y NV NY hNV hNY v
  (@coordinate_basis R v) (@coordinate_basisP R v) (hom_of_linear j).
have hL:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) (D a).
have hfU:=@norm_analytic_open_restriction R X Y NX NY hNX hNY A U f hUA hopen hfA.
have hgA:@norm_analytic R X X NX NX hNX hNX U g.
  rewrite hformula.
  exact (@norm_source_chart_analytic R X Y V NX NY NV hNX hNY hNV U beta Ib ph (D a)
    f hb hi hp hL hfU).
have hGA:=@norm_analytic_inverse_from_first R X X NX NX hNX hNX C U G g
  hGU hgC hgG hGg (norm_diffeomorphism_inverse_class hchart) hgA.
pose V0:=@constant_rank_parameter_domain R v l g a e.
have hVOpen u (hu:V0 u):norm_domain_interior NV V0 u.
  exact (@norm_open_ball_domain_interior R V NV hNV
    (@euclidean_first_block_map R v l (g a)) e u hu).
pose slice:=fun u:V=>Ib u+Jb (qb (g a)).
have hsA:@norm_analytic R V X NV NX hNV hNX V0 slice.
  exact (norm_analytic_add (@norm_bounded_linear_analytic R V X NV NX hNV hNX V0 hVOpen Ib hi)
    (@norm_constant_analytic R V X NV NX hNV hNX V0 hVOpen (Jb (qb (g a))))).
have hSlice u (hu:V0 u):C (slice u).
  apply:(proj2 (@euclidean_product_box_coordinates R v l (g a) e u (qb (g a)))).
  split; first exact hu.
  by rewrite subrr inner_norm0.
have hGs:=@norm_analytic_compose_on R V X X NV NX NX hNV hNX hNX V0 C slice G hSlice hsA hGA.
have hpsia:=@norm_analytic_compose_on R V X Y NV NX NY hNV hNX hNY V0 A
  (fun u=>G (slice u)) f (fun u hu=>hUA _ (hGU _ (hSlice u hu))) hGs hfA.
have hC:=@constant_rank_chart_from_product_source R v l n A U f D a 1%N p j g G e
  hk1 (hf 1%N) hD hP he haU hU hchart (fun x _=>hprefix x).
have hshears:=@norm_section_shears_analytic R Y V NY NV hNY hNV ph (hom_of_linear j) V0 psi
  hp hj hpsia.
exists U,e,p,j,g,G,psi; split; first exact hC.
split; first exact hgA.
split; first exact hGA.
split; first exact hpsia.
exact hshears.
Qed.
End AnalyticConstantRank.
