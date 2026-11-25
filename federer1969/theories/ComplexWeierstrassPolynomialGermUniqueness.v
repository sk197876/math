(** Federer (1969), 3.4.12, p. 339: the original
    monic polynomial germ determines every transverse coefficient
    germ. Reuse exact local germ equality, the original coordinate
    splitting and finite coefficient uniqueness on short real lines. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormMetric NormDifferentialUP NormRegularity NormAnalyticLocal
  NormOpenDomainLaws NormLinearDomainLaws NormBoundedLinearTopology NormTaylorLineValues
  LocalGermUP LocalGermSealed HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws ComplexWeierstrassPreparationUP
  NormWeierstrassFiniteLocalCoefficients ComplexRealPowerSum WeierstrassFiniteFamilyExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Uniqueness.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation KR:=(restricted_space (ComplexScalars.embed R) K).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNKR:=(complex_norm_real hNK).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_polynomial_germ_coefficients_unique]: all
    original transverse germs are uniquely determined by the original
    polynomial germ and xi, extending 3.4.6(2), p. 322, under
    3.4.12, p. 339. The short lines use the same
    original direction; no coefficient uniqueness is a premise. *)
Theorem complex_weierstrass_polynomial_germ_coefficients_unique v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) k
    (W W':@holomorphic_germ_ring R X NX hNXR 0)
    (Wi Wi':'I_k->@holomorphic_germ_ring R K NK hNKR 0):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @is_complex_weierstrass_polynomial_germ R X K NX NK hNXR hNKR xi projection k W Wi ->
  @is_complex_weierstrass_polynomial_germ R X K NX NK hNXR hNKR xi projection k W' Wi' ->
  W=W' ->forall i,Wi i=Wi' i.
Proof.
move=>hSplit [w [hRepW [c [hC [_ [U [haU [hw hWValues]]]]]]]]
  [w' [hRepW' [c' [hC' [_ [V [haV [hw' hWValues']]]]]]]] hEqual i.
pose TX:=Topological.clone (real_norm_metric_space hNXR) _.
pose TK:=Topological.clone (real_norm_metric_space hNKR) _.
pose PX:=@holomorphic_representative_type R X NX hNXR 0.
pose PK:=@holomorphic_representative_type R K NK hNKR 0.
have hGX:=@LocalGerms.laws TX C PX (@holomorphic_representative_value R X NX hNXR 0) 0.
have hGK:=@LocalGerms.laws TK C PK (@holomorphic_representative_value R K NK hNKR 0) 0.
have hGermEqual:holomorphic_germ w=holomorphic_germ w' by rewrite hRepW hRepW' hEqual.
have [O [hO [haO hValues]]]:=(local_germ_equality hGX _ _).1 hGermEqual.
have hOInterior x (hx:O x):@norm_domain_interior R XR NX O x.
  have hNeighbourhood:=hO;rewrite openE in hNeighbourhood.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNXR O x).2 (hNeighbourhood x hx).
pose D:=fun x=>U x /\V x /\O x.
have haD:D 0 by split;[exact:haU|split;[exact:haV|exact:haO]].
have hD x (hx:D x):@norm_domain_interior R XR NX D x.
  exact:norm_domain_intersection_interior
    ((norm_analytic_class_all_orders hw.1 0%N).1 x hx.1).1
    (norm_domain_intersection_interior ((norm_analytic_class_all_orders hw'.1 0%N).1 x hx.2.1).1
      (hOInterior x hx.2.2)).
have [rho [hRho hBall]]:=hD 0 haD.
pose B:set K:=fun z=>NK z<rho.
have haB:B 0 by rewrite /B (real_seminorm_zero hNKR.1).
have hB:@open (real_norm_metric_space hNKR) B.
  rewrite openE=>z hz;apply:(@norm_domain_interior_neighbourhood R KR NK hNKR B z).1.
  have hBallOpen:=@norm_open_ball_domain_interior R KR NK hNKR 0 rho z.
  rewrite subr0 in hBallOpen.
  have hDomain:(fun x:K=>is_true (NK (x-0)<rho))=B by apply:funext=>x;rewrite subr0.
  rewrite hDomain in hBallOpen;exact:hBallOpen hz.
rewrite -(hC i) -(hC' i);apply/(local_germ_equality hGK).
exists B;split;first exact:hB.
split;first exact:haB.
move=>z hz.
have ha:D (inclusion z).
  have hSmall:NX (inclusion z)<rho by rewrite (complex_weierstrass_transverse_inclusion_norm hSplit).
  have hh:=hBall (inclusion z) hSmall;by rewrite add0r in hh.
have [radius [hRadius hLineBall]]:=hD (inclusion z) ha.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R XR NX hNXR v radius hRadius.
have hLocal (t:R) (ht:`|t|<delta):
    (\sum_(j<k) t^+j*:(holomorphic_representative_value (c j) z:CR))=
      \sum_(j<k) t^+j*:(holomorphic_representative_value (c' j) z:CR).
  have hd:D ((inclusion z:XR)+t*:(v:XR)):=hLineBall _ (hSmall t ht).
  have hEquation:=hValues ((inclusion z:XR)+t*:(v:XR)) hd.2.2.
  have hPoint:((inclusion z:XR)+t*:(v:XR):XR)=ComplexScalars.embed R t*:v+inclusion z:=addrC _ _.
  rewrite (hWValues _ hd.1) (hWValues' _ hd.2.1) hPoint
    (complex_weierstrass_line_functional_coordinate hSplit)
    (complex_weierstrass_line_transverse_coordinate hSplit) in hEquation.
  have hSums:
      (\sum_(j<k) (ComplexScalars.embed R t)^+j*holomorphic_representative_value (c j) z)=
      \sum_(j<k) (ComplexScalars.embed R t)^+j*holomorphic_representative_value (c' j) z.
    exact:addrI hEquation.
  have hLeft:(\sum_(j<k) (ComplexScalars.embed R t)^+j*holomorphic_representative_value (c j) z)=
      \sum_(j<k) t^+j*:(holomorphic_representative_value (c j) z:CR).
    apply:eq_bigr=>j _.
    change ((ComplexScalars.embed R t)^+j*holomorphic_representative_value (c j) z=
      ComplexScalars.embed R (t^+j)*holomorphic_representative_value (c j) z).
    by rewrite rmorphXn.
  have hRight:(\sum_(j<k) (ComplexScalars.embed R t)^+j*holomorphic_representative_value (c' j) z)=
      \sum_(j<k) t^+j*:(holomorphic_representative_value (c' j) z:CR).
    apply:eq_bigr=>j _.
    change ((ComplexScalars.embed R t)^+j*holomorphic_representative_value (c' j) z=
      ComplexScalars.embed R (t^+j)*holomorphic_representative_value (c' j) z).
    by rewrite rmorphXn.
  by rewrite hLeft hRight in hSums.
have [a hA]:=@weierstrass_finite_family_extension C k (fun j=>holomorphic_representative_value (c j) z) 0.
have [b hBValue]:=@weierstrass_finite_family_extension C k (fun j=>holomorphic_representative_value (c' j) z) 0.
have hPolynomial:exists r:R,0<r /\forall t:R,`|t|<r ->
    (\sum_(j<k) t^+j*:(a j:CR))=\sum_(j<k) t^+j*:(b j:CR).
  exists delta;split;first exact:hDelta.
  move=>t ht.
  have hFirst:(\sum_(j<k) t^+j*:(a j:CR))=\sum_(j<k) t^+j*:(holomorphic_representative_value (c j) z:CR).
    apply:eq_bigr=>j _;by rewrite hA.
  have hSecond:(\sum_(j<k) t^+j*:(b j:CR))=\sum_(j<k) t^+j*:(holomorphic_representative_value (c' j) z:CR).
    apply:eq_bigr=>j _;by rewrite hBValue.
  rewrite hFirst hSecond;exact:hLocal t ht.
have hCoefficient:=@norm_weierstrass_finite_local_coefficients R CR N hN k a b hPolynomial i (ltn_ord i).
by rewrite hA hBValue in hCoefficient.
Qed.
End Uniqueness.
