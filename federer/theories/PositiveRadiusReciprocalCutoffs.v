(** Federer (1969), 3.3.15, p. 299: countable strict-margin
    description of the actual positive-radius upper density levels. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PositiveRadiusLimits ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedRealOrderTopology ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_radius_upper_reciprocalE]: cofinal-radius
    support for the Borel upper-density sets used in Federer 3.3.15,
    p. 299, with the literal upper limit of 2.10.19, p. 181.
    All positive real radii remain; reciprocal cutoffs only form a
    cofinal description of their original supremum/infimum. *)
Lemma positive_radius_upper_reciprocalE (R:realType) (f:R->\bar R):
  positive_radius_upper_limit f=extended_real_inf
    [set q|exists i:nat,q=extended_real_sup
      (positive_radius_values f (((i.+1)%:R:R)^-1)%R)].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_inf_greatest=>q [i ->].
  apply:positive_radius_upper_le_level.
  by rewrite invr_gt0 ltr0n.
- rewrite /positive_radius_upper_limit.
  apply:extended_real_inf_greatest=>q [e [he ->]].
  have [i hSmall]:=positive_reciprocal_nat_small he.
  apply:le_trans (extended_real_inf_lower (ex_intro _ i (erefl _))) _.
  apply:extended_real_sup_least=>v [r [hr ->]].
  apply:extended_real_sup_upper; exists r; split; last by [].
  apply/andP; split; first exact:(andP hr).1.
  exact:lt_trans (andP hr).2 hSmall.
Qed.

(** Source for [positive_radius_supremum_strict_level]: supporting
    strict-radius witnesses for the Borel upper-density argument of
    Federer 3.3.15, p. 299. A strict bound below an actual extended
    supremum has an actual positive-radius witness; empty domains
    and infinite values retain the original order conventions. *)
Lemma positive_radius_supremum_strict_level (R:realType) (P:Type)
    (f:P->R->\bar R) (delta:R) (b: \bar R):
  [set x:P|(b<extended_real_sup (positive_radius_values (f x) delta))%E]=
    [set x:P|exists r:R,(0<r<delta) /\(b<f x r)%E].
Proof.
apply/seteqP; split=>x.
- move=>hAbove; case:(pselect (exists r:R,(0<r<delta) /\(b<f x r)%E))=>h.
  + exact:h.
  + exfalso; have hBound:(extended_real_sup (positive_radius_values (f x) delta)<=b)%E.
      apply:extended_real_sup_least=>v [r [hr ->]].
      rewrite leNgt; apply/negP=>hValue; apply:h; by exists r.
    by have:=lt_le_trans hAbove hBound; rewrite ltxx.
- move=>[r [hr hValue]]; apply:lt_le_trans hValue _.
  apply:extended_real_sup_upper; by exists r.
Qed.

(** Source for [positive_radius_upper_strict_superlevel]: supporting
    the Borel upper-density level sets in Federer 3.3.15, p. 299.
    The countable formula retains a strict threshold margin and all
    reciprocal cutoff indices, as in the corrected order argument
    of 3.3.2, p. 288 (published erratum pp. 5–6). It is an
    order-theoretic expansion, not a correction to 3.3.15. *)
Theorem positive_radius_upper_strict_superlevel (R:realType) (P:Type)
    (f:P->R->\bar R) (b:R):
  [set x:P|(b%:E<positive_radius_upper_limit (f x))%E]=
    \bigcup_j \bigcap_i [set x:P|
      ((((b+((j.+1)%:R:R)^-1)%R)%:E<extended_real_sup
        (positive_radius_values (f x) (((i.+1)%:R:R)^-1)%R)))%E].
Proof.
apply/seteqP; split=>x.
- move=>hLower.
  have [q [hBQ hQU]]:=@extended_rationals_order_dense R _ _ hLower.
  have hGap:(0<ratr q-b)%R by move:hBQ; rewrite lte_fin subr_gt0.
  have [j hSmall]:=positive_reciprocal_nat_small hGap.
  exists j; first exact:Logic.I.
  move=>i _.
  have hMargin:(((b+((j.+1)%:R:R)^-1)%R)%:E<(ratr q:R)%:E)%E.
    rewrite lte_fin; by move:hSmall; rewrite ltrBrDl addrC.
  apply:lt_le_trans (lt_trans hMargin hQU) _.
  apply:positive_radius_upper_le_level.
  by rewrite invr_gt0 ltr0n.
- move=>[j _ hAll].
  have hMargin:(b<b+((j.+1)%:R:R)^-1)%R by rewrite ltrDl invr_gt0 ltr0n.
  have hGap:(b%:E<((b+((j.+1)%:R:R)^-1)%R)%:E)%E by rewrite lte_fin.
  apply:lt_le_trans hGap _.
  rewrite positive_radius_upper_reciprocalE.
  apply:extended_real_inf_greatest=>v [i ->]; exact:ltW (hAll i Logic.I).
Qed.
