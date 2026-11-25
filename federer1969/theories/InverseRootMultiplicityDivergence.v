(** Federer (1969), 3.2.7, p. 246: supporting
    divergence calculation for the reciprocal-root weight.
    A count of at least n below c^2/n^2,
    multiplied by y^(-1/2), gives a uniform positive
    mass on each disjoint squared dyadic band. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralBounds LebesgueScalarMeasure EuclideanLebesgueBoxes
  MeasureDensity MeasureDensityUP NonnegativeDensitySetLowerBound DensityDisjointMassDivergence PositiveDyadicBands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inverse_root_multiplicity_upper_integral_infinite]:
    divergence estimate for the third example in
    Federer 3.2.7, p. 246. The explicit
    comparison uses only integer multiplicity bounds,
    scalar square roots and interval length; it
    assumes no power-integral formula or improper integral. *)
Theorem inverse_root_multiplicity_upper_integral_infinite (R:realType)
    (H:R->extended_real_line R) (c:R):
  (0<c)%R -> (forall y,0<=H y) ->
  (forall n:nat,(0<n)%N -> forall y:R,(0<y)%R ->
    (y<=(c/n%:R)^+2)%R -> ((n%:R/Num.sqrt y)%R%:E<=H y)) ->
  measure_upper_integral (@lebesgue_scalar_measure R) (partial_function_total H)=+oo.
Proof.
move=>hc hp hGrowth.
pose mu:=@lebesgue_scalar_measure R; have hm:=lebesgue_scalar_is_measure R.
pose E:=@positive_dyadic_band R c.
pose nu:=measure_with_density mu (partial_function_total H).
have hD:(0<3*c/4)%R by apply:divr_gt0; [nra|by rewrite ltr0n].
apply:(@density_disjoint_uniform_mass_divergence R [the choiceType of real_line_metric R]
  mu hm H E (3*c/4)%R hp).
- move=>k; exact:lebesgue_scalar_open_interval_measurable.
- exact:positive_dyadic_bands_disjoint hc.
- exact hD.
- move=>k.
  pose n:=(2^k)%N; pose r:=@positive_dyadic_radius R c k.
  have hn:(0<n)%N by rewrite /n expn_gt0.
  have hnR:(0<(n%:R:R))%R by rewrite ltr0n.
  have hr:(0<r)%R:=positive_dyadic_radius_positive k hc.
  have hcK:(0<n%:R/r)%R by rewrite divr_gt0.
  have hPoint y:E k y -> (n%:R/r)%R%:E<=H y.
    move=>hy.
    have hy':=hy; move:hy'; rewrite /E /positive_dyadic_band /= in_itv /= =>/andP[hyL hyU].
    have hrNext:(positive_dyadic_radius c k.+1=r/2)%R:=positive_dyadic_radius_successor c k.
    have hy0:(0<y)%R by have hh:=exprn_ge0 2 (ltW (positive_dyadic_radius_positive k.+1 hc)); lra.
    have hyBound:(y<=(c/n%:R)^+2)%R:=ltW hyU.
    have hGrow:=hGrowth n hn y hy0 hyBound.
    have hsPos:(0<Num.sqrt y)%R by rewrite sqrtr_gt0.
    have hs:=sqr_sqrtr (ltW hy0).
    have hyR:(y<=r^+2)%R:=ltW hyU.
    have hsBound:(Num.sqrt y<=r)%R by nra.
    have hInv:(r^-1<=(Num.sqrt y)^-1)%R by rewrite (@lef_pV2 R _ _ hr hsPos).
    have hCoeff:(n%:R/r<=n%:R/Num.sqrt y)%R:=ler_wpM2l (ltW hnR) hInv.
    apply:le_trans _ hGrow; by rewrite lee_fin.
  have hBound:=@nonnegative_density_set_lower_bound R [the choiceType of real_line_metric R]
    mu nu hm H (E k) (n%:R/r)%R (measure_with_density_laws mu (partial_function_total H)) hp hcK hPoint.
  have hOrder:((positive_dyadic_radius c k.+1)^+2<=r^+2)%R.
    rewrite positive_dyadic_radius_successor; change ((r/2)^+2<=r^+2)%R; nra.
  have hLength:mu (E k)=((r^+2-(positive_dyadic_radius c k.+1)^+2)%R)%:E.
    exact (lebesgue_scalar_open_interval hOrder).
  rewrite hLength -EFinM in hBound.
  have hMass:((n%:R/r)*(r^+2-(positive_dyadic_radius c k.+1)^+2)=3*c/4)%R.
    rewrite positive_dyadic_radius_successor /r /positive_dyadic_radius /n !expr2.
    have hc0:(c!=0)%R by rewrite gt_eqF.
    have hn0:((((2^k)%N)%:R:R)!=0)%R by rewrite pnatr_eq0 expn_eq0.
    by field; rewrite ?(negbTE hc0) ?(negbTE hn0).
  rewrite hMass in hBound; exact hBound.
Qed.
