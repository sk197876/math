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
  EuclideanBoxFibreFactorisation EuclideanBoxSections NormSectionDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section GenericSection.
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


(** Source for [generic_rank_section_exists]: the class-k section psi,
    the identity p psi=id, the factorisation f=psi p f and the
    normalization Dpsi[(p f)(a)]=p* in Federer 3.1.18, p. 230.
    This assembles the fibre argument from the proved source chart. *)
Theorem generic_rank_section_exists (A U:set X) (f:X->Y) (D:X->Hom X Y) a k
    (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) e :
  (1<=k)%N -> norm_class hNX hNY A f k ->
  is_norm_class_one_field NX NY A f D ->
  is_linear_range_projection BY (D a) p j -> 0<e -> U a ->
  (forall x, U x -> A x /\ has_linear_rank (D x) v /\
    has_linear_rank (hom_comp (hom_of_linear p) (D x)) v) ->
  is_norm_diffeomorphism hNX hNX U (@euclidean_product_box R v l (g a) e) g G k ->
  (forall x, U x -> rb (g x)=p (f x)) ->
  exists psi:V->Y,
    norm_class hNV hNY (fun u=>NV (u-rb (g a))<e) psi k /\
    (forall u, NV (u-rb (g a))<e -> p (psi u)=u) /\
    (forall x, U x -> f x=psi (p (f x))) /\
    psi=(fun u=>f (G (Ib u+Jb (qb (g a))))) /\
    psi (rb (g a))=f a /\
    has_norm_differential NV NY (fun u=>NV (u-rb (g a))<e)
      psi (rb (g a)) (hom_of_linear j).
Proof.
move=>hk hf hD hP he haU hU hchart hprefix.
pose c:=g a.
pose C:=@euclidean_product_box R v l c e.
pose V0:=fun u:V=>NV (u-rb c)<e.
pose ph:=hom_of_linear p.
pose F:=fun z=>f (G z).
pose psi:=fun u=>F (Ib u+Jb (qb c)).
have hgc:=@norm_diffeomorphism_forward_class R X X NX NX hNX hNX U C g G k hchart.
have hGc:=@norm_diffeomorphism_inverse_class R X X NX NX hNX hNX U C g G k hchart.
have hg0:=@norm_class_continuous R X X NX NX hNX hNX U g k hgc.
have hopen x (hx:U x):norm_domain_interior NX U x:=(@hg0 x hx).1.
have hUA x (hx:U x):A x:=(hU x hx).1.
have hfU:=@norm_class_open_restriction R X Y NX NY hNX hNY A U f k hUA hopen hf.
have hDU:=@norm_class_one_field_open_restriction R X Y NX NY A U f D hUA hopen hD.
have [Dg hDg]:=(@norm_class_firstP R X X NX NX hNX hNX U g).1
  (@norm_class_lower R X X NX NX hNX hNX U g k 1%N hk hgc).
have [DG hDG]:=(@norm_class_firstP R X X NX NX hNX hNX C G).1
  (@norm_class_lower R X X NX NX hNX hNX C G k 1%N hk hGc).
have hgC x (hx:U x):C (g x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX U C g G k hchart x hx.
have hGU z (hz:C z):U (G z):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U C g G k hchart z hz.
have hgG z (hz:C z):g (G z)=z:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U C g G k hchart z hz.
have hGg x (hx:U x):G (g x)=x:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX U C g G k hchart x hx.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) ph.
have hr:=@norm_finite_linear_bounded R X V NX NV hNX hNV (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) rb.
have hker x (hx:U x) z:ph (D x z)=0 -> D x z=0.
  exact (@linear_composition_equal_rank_kernel R X Y V (D x) ph v
    (hU x hx).2.1 (hU x hx).2.2 z).
have hcomp:=@norm_constant_rank_composite_differential R X Y V NX NY NV hNX hNY hNV
  U C f g G D Dg DG ph rb hDU hDg hDG hp hr hgC hGU hgG hprefix hker.
have hFc:=@norm_class_compose_on R X X Y NX NX NY hNX hNX hNY C U G f k hGU hGc hfU.
have hpsic:=@euclidean_box_section_class R v l Y NY hNY c e F k he hFc.
have hsec u (hu:V0 u):ph (psi u)=u.
  pose y:=Ib u+Jb (qb c).
  have hy:C y.
    apply: (@euclidean_product_box_coordinates R v l c e u (qb c)).2; split=>//.
    by rewrite subrr inner_norm0.
  have hh:=hprefix (G y) (hGU y hy).
  rewrite (hgG y hy) /y linearD /= euclidean_first_block_injectionK
    euclidean_first_block_last_injection addr0 in hh.
  exact: esym hh.
have hDF z (hz:C z):has_norm_differential NX NY C F z (hom_comp (D (G z)) (DG z)).
  exact: (hcomp z hz).1.
have hkill z (hz:C z) w:hom_comp (D (G z)) (DG z) (Jb w)=0.
  exact: (hcomp z hz).2 (@euclidean_first_block_last_injection R v l w).
have hfactor:=@euclidean_box_fibre_factorisation R v l Y NY hNY c e F
  (fun z=>hom_comp (D (G z)) (DG z)) he hDF hkill.
have hc:C c:=hgC a haU.
have hGcbase:G c=a:=hGg a haU.
have hdFbase:has_norm_differential NX NY C F c (hom_comp (D a) (DG c)).
  by move: (hDF c hc); rewrite hGcbase.
have hdpsi:=@euclidean_box_section_differential_at_center R v l Y NY hNY c e F
  (hom_comp (D a) (DG c)) he hdFbase.
pose J:=hom_comp (hom_comp (D a) (DG c)) Ib.
have hJsec:=@norm_section_derivative_right_inverse R V Y NV NY hNV V0 psi ph
  (rb c) J hp hsec hdpsi.
have hJIm u:exists x, D a x=J u.
  exists (DG c (Ib u)); by rewrite /J !hom_compE.
have hJ:=@range_projection_section_unique R X Y BY (D a) v p j J hP hJsec hJIm.
change (has_norm_differential NV NY V0 psi (rb c) J) in hdpsi.
rewrite hJ in hdpsi.
exists psi; split=>//; split; first exact hsec.
split.
- move=>x hx; have hh:=hfactor (g x) (hgC x hx).
  rewrite /F (hGg x hx) (hprefix x hx) in hh; exact hh.
- split; first by [].
  split; last exact hdpsi.
  rewrite /psi -(euclidean_block_linear_decomposition c) /F hGcbase.
  by [].
Qed.
End GenericSection.
