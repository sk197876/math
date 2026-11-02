(** Federer (1969), 3.1.24, pp. 238–239:
    norm limits of the higher differential series, in the
    abstract continuous multilinear spaces of 3.1.11, p. 219.
    Pointwise limits of a Cauchy family satisfy a uniform
    product-weighted error estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_multilinear_cauchy_uniform]: supporting
    convergence of the differential series in Federer 3.1.24,
    pp. 238–239. A Cauchy family with pointwise limits
    converges uniformly after weighting by the product of
    input norms. The empty argument family and zero input
    vectors are included without division by their norms. *)
Theorem continuous_multilinear_cauchy_uniform (R:realType) k
    (X Y Z:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ev:{ffun 'I_k->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN)
    (F:set_system (real_norm_metric_space (continuous_multilinear_norm_is_norm hNY hZ)))
    (g:{ffun 'I_k->X}->Y) (PF:ProperFilter F) :
  cauchy F ->
  (forall u,(fun z=>(ev u z:real_norm_metric_space hNY)) @ F -->
    (g u:real_norm_metric_space hNY)) ->
  forall e:R,0<e -> exists2 U,F U & forall z,U z -> forall u,
    NY (ev u z-g u)<=e*\prod_(i<k) NX (u i).
Proof.
move=>hc hg e he.
pose E:=real_norm_metric_space (continuous_multilinear_norm_is_norm hNY hZ).
pose T:=real_norm_metric_space hNY.
have FF:Filter F:=@filter_filter _ F PF.
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
have [c hcB]:=proj1 (@cauchyP R E F PF) hc (e/2) he2.
exists (ball c (e/2))=>// z hz u.
apply/ler_addgt0Pr=>d hd.
have hn:nbhs (g u:T) [set y:T|mdist (g u:T) y<d].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (g u:T) _)).
  by exists d=>// y hy.
have hF:=hg u _ hn.
have [w [hw hgw]]:=@filter_ex E F PF _ (@filterI E F FF _ _ hcB hF).
have hzw:mdist (z:E) w<e.
  move:hz hw; rewrite !ballEmdist /= =>h1 h2.
  apply: le_lt_trans (metric_triangle z c w) _.
  rewrite metric_sym (splitr e); exact: ltrD h1 h2.
have hprod:0<=\prod_(i<k) NX (u i).
  apply: prodr_ge0=>i _; exact: real_seminorm_nonnegative hNX.1 _.
have hzwg:NY (ev u z-ev u w)<=e*\prod_(i<k) NX (u i).
  have hh:=multilinear_operator_bound (continuous_multilinear_norm_laws hZ (z-w)) u.
  rewrite linearB /= in hh.
  apply: le_trans hh _.
  exact (ler_wpM2r hprod (ltW hzw)).
have hwg:NY (ev u w-g u)<d.
  change (is_true (NY (g u-ev u w)<d)) in hgw.
  by rewrite (real_seminorm_subtract hNY.1).
have hid:ev u z-g u= (ev u z-ev u w)+(ev u w-g u).
  by rewrite addrA subrK.
rewrite hid; apply: ltW; apply: le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
exact: ler_ltD hzwg hwg.
Qed.
