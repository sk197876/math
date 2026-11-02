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
  GenericRankSourceChart NormConstantRankComposite LinearRankComposition
  EuclideanBoxFibreFactorisation EuclideanBoxSections NormSectionDerivative
  GenericRankSection NormSectionShear NormSectionShearDifferential ConstantRankChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ChartAssembly.
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



(** Source for [constant_rank_chart_from_product_source]: the full
    target normal form and Dh[f(a)]=identity in Federer 3.1.18,
    p. 230, assembled from the source diffeomorphism and its
    equal-rank neighbourhood. This proves the abstract chart laws for
    the exact displayed section, rather than assuming a normal form. *)
Theorem constant_rank_chart_from_product_source (A U:set X) (f:X->Y) (D:X->Hom X Y) a k
    (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) e :
  (1<=k)%N -> norm_class hNX hNY A f k ->
  is_norm_class_one_field NX NY A f D ->
  is_linear_range_projection BY (D a) p j -> 0<e -> U a ->
  (forall x, U x -> A x /\ has_linear_rank (D x) v /\
    has_linear_rank (hom_comp (hom_of_linear p) (D x)) v) ->
  is_norm_diffeomorphism hNX hNX U (@euclidean_product_box R v l (g a) e) g G k ->
  (forall x, U x -> rb (g x)=p (f x)) ->
  @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G
    (fun u=>f (G (Ib u+Jb (qb (g a))))).
Proof.
move=>hk hf hD hP he haU hU hchart hprefix.
pose c:=g a.
pose C:=@euclidean_product_box R v l c e.
pose psi:=fun u:V=>f (G (Ib u+Jb (qb c))).
pose B:=constant_rank_parameter_domain g a e.
pose T:=constant_rank_target_domain g a e p.
pose ph:=hom_of_linear p.
pose jh:=hom_of_linear j.
pose h:=@norm_section_shear R Y V ph jh psi.
pose H:=@norm_section_shear_inverse R Y V ph jh psi.
have [psi0 [hpsic [hsec [hfactor [hformula [hbase hdpsi]]]]]]:=
  @generic_rank_section_exists R v l n A U f D a k p j g G e
    hk hf hD hP he haU hU hchart hprefix.
change (psi0=psi) in hformula.
rewrite hformula in hpsic hsec hfactor hbase hdpsi.
have hUA x (hx:U x):A x:=(hU x hx).1.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) ph.
have hj:=@norm_finite_linear_bounded R V Y NV NY hNV hNY v
  (@coordinate_basis R v) (@coordinate_basisP R v) jh.
have hpj:cancel jh ph:=range_projection_cancel hP.
have htarget:=@norm_section_shear_diffeomorphism R Y V NY NV hNY hNV ph jh
  hp hj hpj B psi k hpsic hsec.
have hgC x (hx:U x):C (g x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX U C g G k hchart x hx.
have hGU z (hz:C z):U (G z):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U C g G k hchart z hz.
have hgG z (hz:C z):g (G z)=z:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U C g G k hchart z hz.
have hTf x (hx:U x):T (f x).
  have hmem:NV (rb (g x)-rb c)<e:=(hgC x hx).1.
  by rewrite (hprefix x hx) in hmem.
have hnormal x (hx:U x):h (f x)=j (rb (g x)).
  rewrite (hprefix x hx) /h /norm_section_shear -(hfactor x hx).
  by rewrite [f x+_]addrC addrK.
have himage:h @` (f @` U)=j @` B.
  apply/seteqP; split=>z.
  - move=>[y [x hx hxy] hyz].
    exists (rb (g x)); first exact: (hgC x hx).1.
    exact (eq_trans (esym (hnormal x hx)) (eq_trans (congr1 h hxy) hyz)).
  - move=>[u hu hju].
    pose y:=Ib u+Jb (qb c).
    have hy:C y.
      apply: (@euclidean_product_box_coordinates R v l c e u (qb c)).2; split=>//.
      by rewrite subrr inner_norm0.
    have hx:U (G y):=hGU y hy.
    have hpref:rb (g (G y))=u.
      by rewrite (hgG y hy) /y linearD /= euclidean_first_block_injectionK
        euclidean_first_block_last_injection addr0.
    exists (f (G y)); first by exists (G y).
    by rewrite (hnormal (G y) hx) hpref.
have hback x (hx:U x):f x=H (j (rb (g x))).
  have hh:=@norm_diffeomorphism_left_inverse R Y Y NY NY hNY hNY T T h H k htarget
    (f x) (hTf x hx).
  by rewrite (hnormal x hx) in hh; exact: esym hh.
have hpbase:p (f a)=rb c:=esym (hprefix a haU).
have hdpsi':has_norm_differential NV NY B psi (ph (f a)) jh.
  by rewrite hpbase.
have hdh:=@norm_section_shear_differential_identity R Y V NY NV hNY hNV ph jh B psi
  (f a) k hp hj hpj hpsic hsec (hTf a haU) hdpsi'.
by constructor.
Qed.
End ChartAssembly.
