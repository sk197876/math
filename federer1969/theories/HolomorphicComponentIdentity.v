(** Federer (1969), 3.4.12, p. 339, extending the
    continuation step of 3.4.8(12), p. 335: a holomorphic
    equation vanishing on an open part of an original
    holomorphic stratum component vanishes on the whole component.
    Apply the proved real component identity to both actual scalar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexScalarUP ComplexScalarLaws
  ComplexModulus ComplexScalarNorm FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  StandardHermitianCoordinates HolomorphicCoordinateNorm ComplexEuclideanCoordinates ComplexEuclideanCoordinateTopology
  HolomorphicUP HolomorphicSubmanifoldUP HolomorphicSubmanifoldRealCoordinates
  NormDifferentialUP NormBoundedLinearTopology NormAnalyticLocal NormAnalyticUP NormAnalyticLinear NormAnalyticOperations NormAnalyticComplexCoordinates
  AnalyticSubmanifoldUP AnalyticComponentIdentity ContinuousSectionComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Identity.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Y:=(R_n R (n+n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation TX:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
(** Source for [holomorphic_component_identity]: the original
    connected-component continuation used in 3.4.8(12), p. 335,
    under 3.4.12, p. 339. The actual complex equation,
    original domain and component are retained. *)
Theorem holomorphic_component_identity (U S O:set X) (f:X->ComplexScalars.C R) a b:
  @is_holomorphic_submanifold R X NX hNX m S ->S `<=` U ->
  @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) U f ->
  @open TX O ->@connected_component TX S a b ->O b ->
  (forall x,S x ->O x ->f x=0) ->
  forall x,@connected_component TX S a x ->f x=0.
Proof.
move=>hS hSU hF hO hb hbO hZero x hx.
pose u:=@complex_real_coordinate_hom R n.
pose v:=@complex_from_real_coordinate_hom R n.
have hU:=@complex_real_coordinate_hom_continuous R n.
have hV:=@complex_from_real_coordinate_hom_continuous R n.
have hUV:cancel u v:=@complex_real_coordinatesK R n.
have hVU:cancel v u:=@complex_from_real_coordinatesK R n.
pose SReal:set Y:=v @^-1` S.
pose UReal:set Y:=v @^-1` U.
pose OReal:set Y:=v @^-1` O.
have hImage:u @` S = SReal.
  apply/seteqP;split=>y.
  - move=>[z hz hzy];change (S (v y));by rewrite -hzy hUV.
  - move=>hy;exists (v y);[exact:hy|exact:hVU y].
have hBase:S a:=@connected_component_sub TX S b a (@connected_component_sym TX S a b hb).
have hComponents:=(@continuous_section_component_image TY TX v S u hV
  (fun z _=>hU z) (fun z _=>hUV z) a hBase).1.
rewrite hImage in hComponents.
have hB:@connected_component TY SReal (u a) (u b) by rewrite hComponents;exists b.
have hX:@connected_component TY SReal (u a) (u x) by rewrite hComponents;exists x.
have hOReal:@open TY OReal:=@open_comp TY TX v O (fun y _=>hV y) hO.
have hOBase:OReal (u b) by change (O (v (u b)));rewrite hUV.
have hVOpen y (hy:UReal y):norm_domain_interior NY UReal y.
  have hOpen:@open TY UReal:=@open_comp TY TX v U (fun y _=>hV y)
    (norm_analytic_domain_open hF.1).
  rewrite openE in hOpen;exact:(@norm_domain_interior_neighbourhood R Y NY hNY UReal y).2 (hOpen y hy).
have hVAnalytic:=@norm_bounded_linear_analytic R Y XR NY NX hNY hNX UReal hVOpen v
  (@complex_from_real_coordinate_hom_bounded R n).
have hComposite:=@norm_analytic_compose_on R Y XR (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NY NX (@complex_modulus R) hNY hNX (@complex_modulus_real_norm R) UReal U v f
  (fun y hy=>hy) hVAnalytic hF.1.
have hSReal:=holomorphic_submanifold_paired_real_coordinates hS.
have hInside:SReal `<=` UReal by move=>y hy;exact:hSU (v y) hy.
have hRealZero:ComplexScalars.re (f x) = 0.
  have h:=@analytic_component_identity R (n+n) (m+m) UReal SReal OReal
    (fun y=>ComplexScalars.re (f (v y))) (u a) (u b)
    hSReal hInside (norm_analytic_complex_real_part hComposite) hOReal hB hOBase.
  have hZeros:forall y,SReal y ->OReal y ->ComplexScalars.re (f (v y)) = 0.
    move=>y hy hyO;by rewrite (hZero (v y) hy hyO) re_zero.
  have hAt:=h hZeros (u x) hX.
  by rewrite hUV in hAt.
have hImaginaryZero:ComplexScalars.im (f x) = 0.
  have h:=@analytic_component_identity R (n+n) (m+m) UReal SReal OReal
    (fun y=>ComplexScalars.im (f (v y))) (u a) (u b)
    hSReal hInside (norm_analytic_complex_imaginary_part hComposite) hOReal hB hOBase.
  have hZeros:forall y,SReal y ->OReal y ->ComplexScalars.im (f (v y)) = 0.
    move=>y hy hyO;by rewrite (hZero (v y) hy hyO) im_zero.
  have hAt:=h hZeros (u x) hX.
  by rewrite hUV in hAt.
apply:coordinates_injective;by rewrite ?hRealZero ?hImaginaryZero ?re_zero ?im_zero.
Qed.
End Identity.
