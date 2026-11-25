(** General order support for Federer (1969), 3.3.4, p. 289:
    finite sums preserve ordinary nonnegative zero aperture limits. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import PositiveRightOrderLimit RadialRatioZero FinitePositiveRadiusCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_finite_nonnegative_zero_limits]: the finite
    coordinate union argument of Federer 3.3.4, p. 289. Every component
    has its original ordinary limit over all positive real apertures;
    a common cutoff and a single finite error budget give the sum's
    ordinary limit. Empty index types and infinite values away from
    the eventual cutoff cause no exception. *)
Theorem structure_finite_nonnegative_zero_limits (R:realType) (J:finType)
    (f:J->R->\bar R):
  (forall j s,0<s ->(0<=f j s)%E) ->
  (forall j,positive_right_extended_order_limit (f j) 0%E) ->
  positive_right_extended_order_limit (fun s=>\sum_j f j s) 0%E.
Proof.
move=>hNonnegative hLimits; apply:nonnegative_positive_right_limit_zero.
- move=>s hs; apply:sume_ge0=>j _; exact:hNonnegative j s hs.
- move=>e he.
  pose N:=(#|J|)%:R:R.
  have hN:0<=N by rewrite /N ler0n.
  have hN1:0<N+1 by nra.
  pose a:=e/(N+1).
  have ha:0<a by rewrite /a divr_gt0.
  have hEach j:exists d:R,0<d /\forall s:R,0<s<d ->(f j s<a%:E)%E.
    have haE:(0<a%:E)%E by rewrite lte_fin.
    have [d [hd hSmall]]:=(hLimits j).2 a%:E haE.
    exists d; split=>// s /andP [hs hsd]; exact:hSmall s hs hsd.
  have [d [hd hCommon]]:=@finite_common_positive_radius_bound R J
    (fun j s=>(f j s<a%:E)%E) hEach.
  exists d; split=>// s hs hsd.
  have hSmall:0<s<d by apply/andP.
  have hSum:(\sum_j f j s<=\sum_(j:J) a%:E)%E.
    apply:lee_sum=>j _; exact:ltW (hCommon s hSmall j).
  have hValue:(\sum_(j:J) a%:E)=(N*a)%:E.
    by rewrite sumEFin sumr_const cardT /N mulr_natl -cardE.
  have hScalar:N*a<e.
    have hIdentity:(N+1)*a=e by rewrite /a mulrC divfK // gt_eqF.
    nra.
  apply:le_lt_trans hSum _; by rewrite hValue lte_fin.
Qed.
