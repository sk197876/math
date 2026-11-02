(** Removal of epsilon at the end of Federer (1969), 2.9.3, p. 154. The
    finite case rescales reciprocal errors; an infinite right-hand measure
    gives the bound directly. No subtraction or division of pairs of
    infinities is used. Source context: CoveringLowerSublevel.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [scaled_nonnegative_measure_approximation_bound]:
    supporting limit of alpha_phi(A)<=c[beta_phi(A)+epsilon]
    in Federer 2.9.3, p. 154. The nonnegative
    right-hand value may be infinite and c is finite positive. *)
Lemma scaled_nonnegative_measure_approximation_bound (R : realType)
    (a b : \bar R) (c : R) :
  0<=b -> (0<c)%R ->
  (forall e : R, (0<e)%R -> a<=c%:E*(b+e%:E)) -> a<=c%:E*b.
Proof.
move=> hb hc happ; case he: b=> [r| |].
- rewrite -EFinM; apply: extended_real_reciprocal_upper_bound=> n.
  pose e := (((n.+1%:R : R)^-1)/c)%R.
  have hepos : (0<e)%R by rewrite /e divr_gt0 // invr_gt0 ltr0n.
  have h := happ e hepos; rewrite he -EFinD -EFinM in h.
  have hscalar : (c*(r+e)=c*r+(n.+1%:R)^-1)%R.
    by rewrite mulrDr /e mulrCA mulfV ?gt_eqF // mulr1.
  by rewrite hscalar in h.
- have hcE : 0<c%:E by rewrite lte_fin.
  by rewrite muleC (gt0_mulye hcE) leey.
- by move: hb; rewrite he.
Qed.
