(** Federer (1969), 3.4.6(2), p. 322: the
    original transverse coefficients are determined by the
    monic polynomial germ, using actual local equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal
  NormOpenDomainLaws NormLinearDomainLaws NormBoundedLinearTopology NormTaylorLineValues
  LocalGermUP LocalGermSealed AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  WeierstrassTransverseUP WeierstrassTransverseLaws WeierstrassPreparationUP WeierstrassFiniteLocalCoefficients WeierstrassFiniteFamilyExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_polynomial_germ_coefficients_unique]:
    every original coefficient germ Wi is determined
    by the monic polynomial germ W and the supplied
    original xi, 3.4.6(2), p. 322.
    Finite coefficient uniqueness is applied on actual
    short lines through all sufficiently small transverse
    centres; no coefficient uniqueness is assumed. *)
Theorem weierstrass_polynomial_germ_coefficients_unique (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (W W':@analytic_germ_ring R X NX hNX 0)
    (Wi Wi':'I_k->@analytic_germ_ring R K NK hNK 0):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @is_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W Wi ->
  @is_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W' Wi' ->
  W=W' ->forall i,Wi i=Wi' i.
Proof.
move=>hSplit [w [hRepW [c [hC [_ [U [haU [hw hWValues]]]]]]]]
  [w' [hRepW' [c' [hC' [_ [V [haV [hw' hWValues']]]]]]]] hEqual i.
pose TX:=Topological.clone (real_norm_metric_space hNX) _.
pose TK:=Topological.clone (real_norm_metric_space hNK) _.
pose PX:=@analytic_representative_type R X NX hNX 0.
pose PK:=@analytic_representative_type R K NK hNK 0.
have hGX:=@LocalGerms.laws TX R PX (@analytic_representative_value R X NX hNX 0) 0.
have hGK:=@LocalGerms.laws TK R PK (@analytic_representative_value R K NK hNK 0) 0.
have hGermEqual:analytic_germ w=analytic_germ w' by rewrite hRepW hRepW' hEqual.
have [O [hO [haO hValues]]]:=(local_germ_equality hGX _ _).1 hGermEqual.
have hOInterior x (hx:O x):norm_domain_interior NX O x.
  have hNeighbourhood:=hO;rewrite openE in hNeighbourhood.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX O x).2 (hNeighbourhood x hx).
pose D:=fun x=>U x /\V x /\O x.
have haD:D 0 by split;[exact:haU|split;[exact:haV|exact:haO]].
have hD x (hx:D x):norm_domain_interior NX D x.
  exact:norm_domain_intersection_interior
    ((norm_analytic_class_all_orders hw 0%N).1 x hx.1).1
    (norm_domain_intersection_interior ((norm_analytic_class_all_orders hw' 0%N).1 x hx.2.1).1
      (hOInterior x hx.2.2)).
have [rho [hRho hBall]]:=hD 0 haD.
pose B:set K:=fun z=>NK z<rho.
have haB:B 0 by rewrite /B (real_seminorm_zero hNK.1).
have hB:@open (real_norm_metric_space hNK) B.
  rewrite openE=>z hz;apply:(@norm_domain_interior_neighbourhood R K NK hNK B z).1.
  have hBallOpen:=@norm_open_ball_domain_interior R K NK hNK 0 rho z.
  rewrite subr0 in hBallOpen.
  have hDomain:(fun x:K=>is_true (NK (x-0)<rho))=B.
    apply:funext=>x;by rewrite subr0.
  rewrite hDomain in hBallOpen;exact:hBallOpen hz.
rewrite -(hC i) -(hC' i);apply/(local_germ_equality hGK).
exists B;split;first exact:hB.
split;first exact:haB.
move=>z hz.
have ha:D (inclusion z).
  have hSmall:NX (inclusion z)<rho.
    rewrite (weierstrass_transverse_inclusion_norm hSplit);exact:hz.
  have hh:=hBall (inclusion z) hSmall.
  by rewrite add0r in hh.
have [radius [hRadius hLineBall]]:=hD (inclusion z) ha.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R X NX hNX v radius hRadius.
have hLocal t (ht:`|t|<delta):
    (\sum_(j<k) t^+j*analytic_representative_value (c j) z)=
      \sum_(j<k) t^+j*analytic_representative_value (c' j) z.
  have hd:D (inclusion z+t*:v):=hLineBall _ (hSmall t ht).
  have hEquation:=hValues (inclusion z+t*:v) hd.2.2.
  have hPoint:inclusion z+t*:v=t*:v+inclusion z:=addrC _ _.
  rewrite (hWValues _ hd.1) (hWValues' _ hd.2.1) hPoint
    (weierstrass_line_functional_coordinate hSplit)
    (weierstrass_line_transverse_coordinate hSplit) in hEquation.
  exact:addrI hEquation.
have [a hA]:=@weierstrass_finite_family_extension R k
  (fun j=>analytic_representative_value (c j) z) 0.
have [b hBValue]:=@weierstrass_finite_family_extension R k
  (fun j=>analytic_representative_value (c' j) z) 0.
have hPolynomial:exists r:R,0<r /\forall t,`|t|<r ->
    (\sum_(j<k) t^+j*a j)=\sum_(j<k) t^+j*b j.
  exists delta;split;first exact:hDelta.
  move=>t ht.
  have hFirst:(\sum_(j<k) t^+j*a j)=\sum_(j<k) t^+j*analytic_representative_value (c j) z.
    apply:eq_bigr=>j _;by rewrite hA.
  have hSecond:(\sum_(j<k) t^+j*b j)=\sum_(j<k) t^+j*analytic_representative_value (c' j) z.
    apply:eq_bigr=>j _;by rewrite hBValue.
  by rewrite hFirst hSecond;exact:hLocal t ht.
have hCoefficient:=@weierstrass_finite_local_coefficients R k a b hPolynomial i (ltn_ord i).
by rewrite hA hBValue in hCoefficient.
Qed.
