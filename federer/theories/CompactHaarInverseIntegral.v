(** Federer (1969), 3.2.13, p. 251: reversing a
    normalized Haar orbit does not change its integral. This
    is the proved compact-group inversion identity of 2.7.9(6),
    p. 126, with unimodularity from 2.7.12, p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal topology.
From Federer Require Import RealMetricBackground TopologicalGroupUP CovariantIntegralUP HaarIntegralUP
  OrthogonalWedgeIntegrals CompactSupportFunctionUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_haar_inverse_integral]: actual Haar
    integral transport from g^-1 to g, used to compare the
    projection and sphere orbits in Federer 3.2.13, p. 251. *)
Theorem compact_haar_inverse_integral (R:realType) (G:topologicalType)
    (mul:G->G->G) (inv:G->G) (e:G)
    (hG:is_locally_compact_hausdorff_group mul inv e) (theta:set G->\bar R)
    (u:G->R) (q:R):
  compact [set:G] ->is_left_haar_measure mul theta ->compactly_supported_continuous_functions u ->
  is_measure_integral theta (real_total_integrand (u\o inv)) q%:E ->
  is_measure_integral theta (real_total_integrand u) q%:E.
Proof.
move=>hGc [L [hL hm hRep hReg]] hu hi.
have hComp:compactly_supported_continuous_functions (u\o inv).
  split.
  - have hInvCont:continuous inv:=topological_group_inv_continuous (lch_group_topological hG).
    move=>g; exact (continuous_comp (hInvCont g) (hu.1 (inv g))).
  - exact:(subclosed_compact (@real_function_support_closed R G _) hGc (@subsetT _ _)).
have hVal:=EFin_inj (measure_integral_unique (hRep _ hComp) hi).
have hInv:=compact_haar_integral_inversion hG hGc hL hu.
rewrite hInv in hVal.
by rewrite -hVal; exact:hRep u hu.
Qed.
