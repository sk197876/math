(** Supporting interval refinement for Federer (1969), 2.10.7, p. 174, the
    assertion that all positive-cutoff approximating measures agree.
    Subdivide a long interval at a point outside a countable exceptional
    set, discard its zero atom, and telescope the two increment costs.
    Induction on a length budget gives the cost bound for every bounded open
    interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From mathcomp Require Import lra.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit StieltjesInducedUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [interval_increment_subdivision_bound]:
    supporting extension from short to arbitrary
    interval costs in Federer 2.10.7, p. 174.
    Endpoints of the target interval need not
    avoid the exceptional set; only the new
    internal subdivision points must have zero atoms. *)
Theorem interval_increment_subdivision_bound (R : realType) (g : R -> R)
    (mu : set R -> \bar R) (hm : is_measure mu) (C : set R) (d : R) :
  countable C -> (0<d)%R ->
  (forall x, ~ C x -> mu [set x]=0) ->
  (forall a b, (a<b)%R -> (b-a<d)%R -> mu `]a,b[<=(g b-g a)%:E) ->
  forall a b, (a<b)%R -> mu `]a,b[<=(g b-g a)%:E.
Proof.
move=> hC hd hzero hshort.
have hsteps : forall n a b, (a<b)%R -> (b-a<=n%:R*(d/4))%R ->
    mu `]a,b[<=(g b-g a)%:E.
  elim=> [|n ih] a b hab hlen.
  - apply: hshort=> //; move: hlen; rewrite mul0r=> hh; lra.
  - case: (ltP (b-a)%R d)=> hsmall; first exact: hshort hab hsmall.
    have hzrange : (a+d/4<a+d/2)%R by lra.
    have [z [/andP[haz hza] hzC]] := @open_interval_avoid_countable R C (a+d/4)%R (a+d/2)%R hC hzrange.
    have haz' : (a<z)%R by lra.
    have hzb : (z<b)%R by lra.
    have hzshort : (z-a<d)%R by lra.
    have hrest : (b-z<=n%:R*(d/4))%R.
      by move: hlen; rewrite -addn1 natrD mulrDl mul1r=> hh; lra.
    have hfirst := hshort a z haz' hzshort.
    have hlast := ih z b hzb hrest.
    have hfirst' : mu (`]a,z[ `|` [set z])<=(g z-g a)%:E.
      have hc : (`]a,z[ `|` [set z]) `<=` `]a,z[ `|` [set z] by [].
      have hb := measure_binary_cover hm hc.
      rewrite (hzero z hzC) adde0 in hb; exact: le_trans hb hfirst.
    have hcover : `]a,b[ `<=` (`]a,z[ `|` [set z]) `|` `]z,b[.
      move=> x; rewrite /= in_itv /= => /andP[hax hxb].
      case: (ltgtP x z)=> hxz.
      - left; left; by rewrite /= in_itv /= hax hxz.
      - right; by rewrite /= in_itv /= hxz hxb.
      - left; right; exact hxz.
    have hbound := measure_binary_cover hm hcover.
    apply: le_trans hbound _; apply: le_trans (leeD hfirst' hlast) _.
    rewrite -EFinD.
    have heq : (g z-g a+(g b-g z)=g b-g a)%R by lra.
    by rewrite heq.
move=> a b hab.
have hd4 : (0<d/4)%R by rewrite divr_gt0 // ltr0n.
have hnon : (0<=(b-a)/(d/4))%R by rewrite divr_ge0 ?subr_ge0 ?ltW.
have hn := archi_boundP hnon; rewrite ltr_pdivrMr // in hn.
exact: hsteps _ a b hab (ltW hn).
Qed.
