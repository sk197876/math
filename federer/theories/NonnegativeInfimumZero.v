(** Order-theoretic support for the radius-infimum premise in Federer
    (1969), 2.8.15, p. 150, and diameter fineness in 2.8.16, p. 151. A
    nonnegative extended-real set has infimum zero exactly when it has a
    member below every positive finite real number. The proof uses only the
    sealed infimum laws of 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_infimum_zero_iff]: the use of inf{r:B(a,r) in
    F}=0 to find arbitrarily small eligible radii in Federer 2.8.15, p. 150
    This general supporting order lemma also applies to the diameter infimum
    in 2.8.16, p. 151. The empty set has infimum infinity, so does not
    satisfy the condition. *)
Lemma nonnegative_infimum_zero_iff (R : realType) (S : set (\bar R)) :
  (forall x, S x -> 0 <= x) ->
  (extended_real_inf S = 0 <-> forall e : R, (0 < e)%R ->
    exists x, S x /\ x < e%:E).
Proof.
move=> hnonneg; split.
- move=> hi e he.
  apply: contrapT=> hn.
  have hl : e%:E <= extended_real_inf S.
    apply: extended_real_inf_greatest=> x hx.
    rewrite leNgt; apply/negP=> hxe; apply: hn; by exists x.
  by rewrite hi lee_fin leNgt he in hl.
- move=> hsmall.
  have h0 : 0 <= extended_real_inf S by apply: extended_real_inf_greatest.
  have hle : extended_real_inf S <= 0.
    rewrite leNgt; apply/negP=> hpos.
    have [d [hd hb]] : exists d : R, (0 < d)%R /\ d%:E <= extended_real_inf S.
      case hi : (extended_real_inf S)=> [d| |] in hpos *.
      * exists d; split; first by move: hpos; rewrite lte_fin.
        exact: lexx.
      * exists 1%R; split; [exact: ltr01|exact: leey].
      * by [].
    have he : (0 < d/2)%R by rewrite divr_gt0 // ltr0n.
    have [x [hx hxe]] := hsmall (d/2)%R he.
    have hbad := le_lt_trans (le_trans hb (extended_real_inf_lower hx)) hxe.
    rewrite lte_fin ltr_pdivlMr ?ltr0n // in hbad.
    have hdd : (d < d*2)%R by rewrite ltr_pMr // ltr1n.
    by have := lt_trans hdd hbad; rewrite ltxx.
  apply/eqP; by rewrite eq_le h0 hle.
Qed.
