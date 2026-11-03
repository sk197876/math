(** Federer (1969), 3.2.41, printed p. 277, choice of the
    second coordinate cut: an interval's left-cut length is
    max(0,min(b,t)-a). Its continuity is proved before the
    finite-family intermediate-value argument is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureFiniteClosure
  LebesgueScalarMeasure EuclideanLebesgueBoxes TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_interval_left_cut_measurable]: supporting
    measurable coordinate cuts in Federer 3.2.41, p. 277.
    Both the proper and the empty interval cases are allowed. *)
Lemma scalar_interval_left_cut_measurable (R:realType) (a b t:R):
  measure_measurable (@lebesgue_scalar_measure R) (`]a,b[ `&` [set x:R|x<t]).
Proof.
apply:(measure_measurable_intersection (lebesgue_scalar_is_measure R)
  (lebesgue_scalar_open_interval_measurable a b)).
apply:lebesgue_scalar_borel_measurable; apply:open_borel_set; exact:open_lt.
Qed.

(** Source for [scalar_interval_left_cut_length]: supporting actual
    clipped interval length in Federer 3.2.41, p. 277. The
    formula covers cuts below, inside and above the original interval. *)
Lemma scalar_interval_left_cut_length (R:realType) (a b t:R):
  a<b ->@lebesgue_scalar_measure R (`]a,b[ `&` [set x:R|x<t])=
    (Order.max 0 (Order.min b t-a))%:E.
Proof.
move=> hab; case:(leP t a)=>[hta|hat].
- have hEmpty:(`]a,b[ `&` [set x:R|x<t])=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [hx hxt]; have /andP[hax _]:a<x<b by move:hx; rewrite /= in_itv.
    exfalso; have hBad:=lt_le_trans (lt_trans hax hxt) hta; by rewrite ltxx in hBad.
  rewrite hEmpty (measure_empty (lebesgue_scalar_is_measure R)) min_r;
    last exact:le_trans hta (ltW hab).
  by rewrite max_l ?subr_le0.
- case:(leP b t)=>[hbt|htb].
  + have hWhole:(`]a,b[ `&` [set x:R|x<t])=(`]a,b[:set R).
      apply/seteqP; split=> x hx; first exact hx.1.
      split=>//; have /andP[_ hxb]:a<x<b by move:hx; rewrite /= in_itv.
      exact:lt_le_trans hxb hbt.
    have hMin:Order.min b t=b:=min_l hbt.
    have hMax:Order.max 0 (b-a)=b-a.
      apply:max_r; by rewrite subr_ge0; exact:ltW hab.
    by rewrite hWhole (lebesgue_scalar_open_interval (ltW hab)) ?hMin ?hMax.
  + have hInterval:(`]a,b[ `&` [set x:R|x<t])=(`]a,t[:set R).
      apply/seteqP; split=> x; rewrite /= !in_itv /=.
      * move=> [/andP[hax hxb] hxt]; by apply/andP; split.
      * move=> /andP[hax hxt]; split; last exact hxt.
        apply/andP; split=>//; exact:lt_trans hxt htb.
    have hMin:Order.min b t=t:=min_r (ltW htb).
    have hMax:Order.max 0 (t-a)=t-a.
      apply:max_r; by rewrite subr_ge0; exact:ltW hat.
    by rewrite hInterval (lebesgue_scalar_open_interval (ltW hat)) ?hMin ?hMax.
Qed.

(** Source for [scalar_interval_left_cut_continuous]: supporting
    continuity needed to choose b in Federer 3.2.41, p. 277.
    It is a scalar min/max continuity consequence, proved independently
    of the desired cut mass or Brunn--Minkowski comparison. *)
Lemma scalar_interval_left_cut_continuous (R:realType) (a b:R):
  continuous (fun t:real_line_metric R=>
    (Order.max 0 (Order.min b t-a):real_line_metric R)).
Proof.
move=> t; apply:(@continuous_max R [the topologicalType of real_line_metric R]
  (fun _=>0) (fun t=>Order.min b t-a) t); first exact:cvg_cst.
apply:continuousB; last exact:cvg_cst.
apply:(@continuous_min R [the topologicalType of real_line_metric R]
  (fun _=>b) (fun t=>t) t); [exact:cvg_cst|exact:cvg_id].
Qed.
