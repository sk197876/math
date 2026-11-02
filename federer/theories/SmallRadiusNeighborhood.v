(** Small-radius neighborhood estimates for Federer (1969), 2.8.12, pp.
    148–149: mu<xi/2 gives r+s<xi whenever r,s<mu. Xi may be infinity, as
    allowed in 2.8.9. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RadiusCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_half_radius_boundE]: the hypothesis
    mu<xi/2 in Federer 2.8.12, p. 148. For a finite
    real mu, multiplication of xi by the positive real 1/2
    is equivalent to mu+mu<xi, including xi=infinity. *)
Lemma extended_half_radius_boundE (R : realType) (xi : \bar R) (mu : R) :
  (mu%:E < (1/2 : R)%:E * xi)%E = ((mu+mu)%:E < xi)%E.
Proof.
have h2 : (0 < (2 : R))%R by rewrite ltr0n.
have h2E : (0 < (2 : R)%:E)%E by rewrite lte_fin.
have h2f : (2 : R)%:E \is a fin_num by [].
rewrite -(@lte_pmul2l R (2 : R)%:E h2f h2E) muleA -!EFinM mulrA mulr1 mulfV ?gt_eqF // mul1e.
by rewrite mulr_natl.
Qed.

(** Source for [small_radii_meeting_center_near]: the estimate
    rho(a,b)<=r+s<2mu<xi in Federer 2.8.12, p. 149.
    Only radius bounds and the displayed distance bound are used;
    an actual intersection of the balls is not required. *)
Lemma small_radii_meeting_center_near (R : realType) (X : metricType R)
    (xi : \bar R) (mu : R) (Q : set (X*R)) :
  is_bounded_positive_radius_family mu Q ->
  (mu%:E < (1/2 : R)%:E * xi)%E -> forall p q, Q p -> Q q ->
  mdist p.1 q.1 <= p.2+q.2 -> ((mdist p.1 q.1)%:E < xi)%E.
Proof.
move=> hQ hx p q hp hq hd.
have hsmall : p.2+q.2 < mu+mu := ltrD (andP (hQ p hp)).2 (andP (hQ q hq)).2.
rewrite extended_half_radius_boundE in hx.
apply: lt_trans _ hx; rewrite lte_fin; exact: le_lt_trans hd hsmall.
Qed.
