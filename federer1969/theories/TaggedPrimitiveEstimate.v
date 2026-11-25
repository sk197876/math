(** Supporting elementary fundamental-theorem argument for Federer (1969),
    2.6.3(2), pp. 117–118 Primitive increments telescope, while the sum of
    interval lengths is b-a. The tagged sequences are exactly those already
    used for Federer's 2.5.17, pp. 110–111. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import StieltjesSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [tagged_primitive_error_bound]: supporting telescoping
    estimate for the elementary integral calculations in Federer 2.6.3(2),
    pp. 117–118 A cell error bounded by epsilon times its length gives the
    same bound over the whole interval, including a degenerate interval. *)
Lemma tagged_primitive_error_bound (R : realType) (f F : R -> R) (a b d e : R) (w : seq R) :
  is_tagged_partition a b w -> tagged_mesh_lt d w ->
  (forall s u t : R, a <= s -> s <= u -> u <= t -> t <= b -> t-s < d ->
    `|F t-F s-f u*(t-s)| <= e*(t-s)) ->
  `|stieltjes_sum f (fun x => x) w-(F b-F a)| <= e*(b-a).
Proof.
have [n] := ubnP (size w); elim: n w a=> // n ih w a hsize hw hmesh hcell.
case: w hsize hw hmesh=> [|s [|u [|t rest]]] hsize hw hmesh.
- by case: hw=> [_ [h _]].
- have [_ [_ [hs hb]]] := hw.
  have ha : s = a := hs; have hb' : s = b := hb.
  rewrite -ha -hb' /= !subrr.
  by rewrite ?subr0 ?normr0 ?mulr0.
- by case: hw=> [_ [h _]].
- have [t' [rest' [hrest [has [hsu [hut hw']]]]]] := tagged_partition_tail hw.
  case: hrest=> ht hrest'; subst t' rest'.
  have htb : t <= b.
    by have /andP[_] := tagged_partition_points_bounds hw' (tagged_partition_a_mem hw').
  have hsize' : (size (t :: rest) < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  move: hmesh; rewrite tagged_mesh_lt_cons=> /andP[hst hmesh'].
  have hcell' : forall s' u' t' : R, t <= s' -> s' <= u' -> u' <= t' -> t' <= b -> t'-s' < d ->
      `|F t'-F s'-f u'*(t'-s')| <= e*(t'-s').
    move=> s' u' t' hts hsu' hut' htb' hmesh''; apply: hcell=> //.
    rewrite has; exact: le_trans (le_trans hsu hut) hts.
  have htail := ih _ _ hsize' hw' hmesh' hcell'.
  have hasle : a <= s by rewrite has lexx.
  have hfirst := hcell s u t hasle hsu hut htb hst.
  rewrite stieltjes_sum_cons /= has.
  have heq : f u*(t-s)+stieltjes_sum f (fun x => x) (t :: rest)-(F b-F s) =
      -(F t-F s-f u*(t-s))+(stieltjes_sum f (fun x => x) (t :: rest)-(F b-F t)) by ring.
  rewrite heq; apply: le_trans (ler_normD _ _) _; rewrite normrN.
  have hsum := lerD hfirst htail.
  have he : e*(t-s)+e*(b-t)=e*(b-s) by ring.
  by rewrite he in hsum.
Qed.
