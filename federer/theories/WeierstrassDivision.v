(** Federer (1969), 3.4.6(1), pp. 321–324:
    the original Weierstrass division theorem, with no
    supplied transverse splitting or normalized leading coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  AnalyticGermUP AnalyticGermRing WeierstrassRegularUP WeierstrassRegularProperties
  WeierstrassDivisionUP WeierstrassDirectionFunctional WeierstrassTransverseSealed WeierstrassDivisionWithTransverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_division]: for every original
    analytic dividend there are unique quotient and remainder
    germs, and every derivative of the remainder of order
    at least k vanishes in direction v throughout one
    neighbourhood, 3.4.6(1), p. 322. The original
    Banach hypothesis is retained. All normalizations,
    functionals and transverse carriers are local proof witnesses. *)
Theorem weierstrass_division (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX]) k (v:X)
    (Phi Psi:@analytic_germ_ring R X NX hNX 0):
  is_weierstrass_regular_germ Phi k v ->
  exists Q T:@analytic_germ_ring R X NX hNX 0,
    @is_weierstrass_division R X NX hNX k v Phi Psi Q T /\
    forall Q' T',@is_weierstrass_division R X NX hNX k v Phi Psi Q' T' ->Q'=Q /\T'=T.
Proof.
move=>hRegular.
have hV:=@weierstrass_regular_direction_nonzero R X NX hNX Phi k v hRegular.
have [xi [hXi hUnit]]:=@weierstrass_direction_functional_exists R X NX hNX v hV.
pose K:=@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
pose NK:=@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
pose hNK:=@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
pose inclusion:=@WeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
pose projection:=@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.
have hSplit:=@WeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.
exact:(@weierstrass_division_with_transverse R X K NX NK hNX hNK v xi inclusion projection k
  Phi Psi hSplit hXi hRegular).
Qed.
