(** Federer (1969), 3.4.6(2), p. 322: the
    original planar polynomial x^2+y has a genuine
    nonzero transverse coefficient in its opaque preparation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanOwnNormCompleteness
  EuclideanScalarCoordinateMaps EuclideanScalarCoordinateAnalytic NormAnalyticUP NormAnalyticLinear
  NormAnalyticOperations NormAnalyticScalarProducts AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  WeierstrassRegularUP WeierstrassRegularProperties WeierstrassLineRegularity WeierstrassTransverseUP
  WeierstrassTransverseSealed WeierstrassPreparationUP WeierstrassPreparationCandidate WeierstrassPreparationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PlanarExample.
Variable R:realType.
Let X:=[the lmodType R of R_n R 2].
Let NX:=inner_norm (@euclidean_inner_productP R 2).
Let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2).
Let i0:'I_2:=ord0.
Let i1:'I_2:=ord_max.
Let v:X:=[ffun i=>if i==i0 then 1 else 0].
Let e1:X:=[ffun i=>if i==i1 then 1 else 0].
Let xi:Hom X R^o:=euclidean_scalar_coordinate_map i0.
Let yi:Hom X R^o:=euclidean_scalar_coordinate_map i1.
Let hXi:norm_bounded_linear NX (fun r:R^o=>`|r|) xi:=euclidean_scalar_coordinate_bounded i0.
Let hUnit:xi v= 1.
Proof. change (v i0= 1). by rewrite /v ffunE eqxx. Qed.
Let K:=@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
Let NK:=@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
Let hNK:=@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
Let inclusion:=@WeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
Let projection:=@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.
Let hSplit:=@WeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.

(** Source for [weierstrass_nonzero_transverse_regression]:
    the original x^2+y has actual directional order two,
    and its prepared constant transverse coefficient is
    nonzero as an analytic germ, testing 3.4.6(2),
    p. 322. Actual analytic maps, original jets,
    exact polynomial equations and the nonzero transverse
    germ are all proved. *)
Example weierstrass_nonzero_transverse_regression:
  exists phi:analytic_representative_type hNX (0:X),
    analytic_representative_value phi=(fun x=>(x i0)^+2+x i1) /\
    exists hRegular:is_weierstrass_regular_germ (analytic_germ phi) 2%N v,
      @WeierstrassPreparation.multiplier R X NX hNX v xi hXi hUnit (@euclidean_own_norm_complete R 2)
        (analytic_germ phi) 2%N hRegular= 1 /\
      @WeierstrassPreparation.polynomial R X NX hNX v xi hXi hUnit (@euclidean_own_norm_complete R 2)
        (analytic_germ phi) 2%N hRegular=analytic_germ phi /\
      @WeierstrassPreparation.coefficients R X NX hNX v xi hXi hUnit (@euclidean_own_norm_complete R 2)
        (analytic_germ phi) 2%N hRegular ord0<>0.
Proof.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
have hFirst:=@euclidean_scalar_coordinate_analytic R 2 i0.
have hSecond:=@euclidean_scalar_coordinate_analytic R 2 i1.
have hSquare:=@norm_analytic_scalar_power R X NX hNX setT (fun x=>x i0) 2%N hFirst.
have hPhiAN:=@norm_analytic_add R X R^o NX N hNX hN setT
  (fun x=>(x i0)^+2) (fun x=>x i1) hSquare hSecond.
have [phi hPhi]:=@analytic_representative_from_domain R X NX hNX 0 setT
  (fun x=>(x i0)^+2+x i1) (hPhiAN 0 Logic.I).
have hRegular:@is_weierstrass_regular_germ R X NX hNX (analytic_germ phi) 2%N v.
  apply:(@weierstrass_line_regularity R X NX hNX phi 2%N v 1 (erefl true) (oner_neq0 R))=>t.
  have hY:yi v=0.
    change (v i1=0);by rewrite /v ffunE /i0 /i1 /=.
  have hXiLinear:xi (t*:v+0)=t*xi v+xi 0:=hom_linear xi t v 0.
  have hYiLinear:yi (t*:v+0)=t*yi v+yi 0:=hom_linear yi t v 0.
  rewrite addr0 linear0 addr0 hUnit mulr1 in hXiLinear.
  rewrite addr0 linear0 addr0 hY mulr0 in hYiLinear.
  rewrite hPhi.
  change ((xi (t*:v))^+2+yi (t*:v)= 1*t^+2).
  by rewrite hXiLinear hYiLinear addr0 mul1r.
pose transverse:=hom_comp yi inclusion.
have hTransverse:norm_bounded_linear NK N transverse:=norm_bounded_linear_compose
  (weierstrass_transverse_inclusion_bounded hSplit) (euclidean_scalar_coordinate_bounded i1).
have hTransverseAN:=@norm_bounded_linear_analytic R K R^o NK N hNK hN setT
  (fun z _=>norm_full_domain_interior NK z) transverse hTransverse.
have [c0 hC0]:=@analytic_representative_from_domain R K NK hNK 0 setT transverse (hTransverseAN 0 Logic.I).
pose zero:=@analytic_constant_representative R K NK hNK 0 0.
pose c (i:'I_2):analytic_representative_type hNK (0:K):=if i==ord0 then c0 else zero.
have hAtZero i:analytic_representative_value (c i) 0=0.
  rewrite /c;case:(i==ord0)=>//.
  by rewrite hC0 /transverse hom_compE !linear0.
have hCoordinates x:(inclusion (projection x)) i1=x i1.
  have hY:yi v=0.
    change (v i1=0);by rewrite /v ffunE /i0 /i1 /=.
  have hLinear:yi ((-xi x)*:v+x)=(-xi x)*yi v+yi x:=hom_linear yi (-xi x) v x.
  change (yi (inclusion (projection x))=yi x).
  rewrite (weierstrass_transverse_projection_equation hSplit).
  have hReorder:x-(xi x)*:v=(-xi x)*:v+x by rewrite scaleNr addrC.
  by rewrite hReorder hLinear hY mulr0 add0r.
have hMonic x:analytic_representative_value phi x=(xi x)^+2+
    \sum_(i<2) (xi x)^+i*analytic_representative_value (c i) (projection x).
  rewrite hPhi !big_ord_recl big_ord0 /= /c /zero /= hC0 /transverse hom_compE
    /yi /xi /euclidean_scalar_coordinate_map /= ?expr0 ?expr1.
  rewrite hCoordinates;ring.
have hCandidate:=@weierstrass_monic_preparation_candidate R X K NX NK hNX hNK xi projection 2%N phi c hAtZero hMonic.
have [hQ [hW hWi]]:=@WeierstrassPreparation.unique R X NX hNX v xi hXi hUnit
  (@euclidean_own_norm_complete R 2) (analytic_germ phi) 2%N hRegular 1 (analytic_germ phi)
  (fun i=>analytic_germ (c i)) hCandidate.
have hProjectionE1:inclusion (projection e1)=e1.
  rewrite (weierstrass_transverse_projection_equation hSplit).
  have hXiE1:xi e1=0.
    change (e1 i0=0);by rewrite /e1 ffunE /i0 /i1 /=.
  by rewrite hXiE1 scale0r subr0.
have hRegularTransverse:@is_weierstrass_regular_germ R K NK hNK (analytic_germ c0) 1%N (projection e1).
  apply:(@weierstrass_line_regularity R K NK hNK c0 1%N (projection e1) 1 (erefl true) (oner_neq0 R))=>t.
  have hLinear:transverse (t*:projection e1+0)=t*transverse (projection e1)+transverse 0:=
    hom_linear transverse t (projection e1) 0.
  rewrite addr0 linear0 addr0 in hLinear.
  have hValue:transverse (projection e1)= 1.
    rewrite /transverse hom_compE hProjectionE1.
    change (e1 i1= 1);by rewrite /e1 ffunE eqxx.
  by rewrite hC0 hLinear hValue mulr1 expr1 mul1r.
have hNonzero:=@weierstrass_regular_germ_nonzero R K NK hNK (analytic_germ c0) 1%N (projection e1) hRegularTransverse.
exists phi;split;first exact:hPhi.
exists hRegular;split;first exact:esym hQ.
split;first exact:esym hW.
rewrite -(hWi ord0) /c eqxx.
exact:hNonzero.
Qed.
End PlanarExample.
