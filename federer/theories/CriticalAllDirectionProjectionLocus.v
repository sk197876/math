(** Federer (1969), 3.3.20, p. 307: the complete critical eight-direction locus. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import BinaryCantorAllDirectionProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_binary_all_direction_projection_locus]:
    at m= 1/2 the entire printed U is exactly the unit directions
    with |u_1|= 2|u_2| or |u_2|= 2|u_1|, 3.3.20, p. 307.
    The equivalence below applies before restricting to the unit circle. *)
Lemma critical_binary_all_direction_projection_locus (R:realType) (u v:R):
  binary_full_projection_direction (1/4:R) u v <->
    `|u|= 2 * `|v| \/ `|v|= 2 * `|u|.
Proof.
rewrite /binary_full_projection_direction.
have hu:=normr_ge0 u;have hv:=normr_ge0 v.
case:(leP `|v| `|u|)=>hOrder.
- rewrite ?(max_l hOrder) ?(min_r hOrder).
  split;first by move=>[h0 h1];left;lra.
  move=>[hEqual|hEqual];split;lra.
- rewrite ?(max_r (ltW hOrder)) ?(min_l (ltW hOrder)).
  split;first by move=>[h0 h1];right;lra.
  move=>[hEqual|hEqual];split;lra.
Qed.

(** Source for [critical_binary_overlap_direction_length]: every
    original critical unit direction in U has full projection length
    3/sqrt(5), 3.3.20, p. 307. All signs and both coordinate
    orders are retained; the actual positive square root fixes the value. *)
Lemma critical_binary_overlap_direction_length (R:realType) (u v:R):
  u^+2+v^+2= 1 ->binary_full_projection_direction (1/4:R) u v ->
  `|u|+ `|v|= 3/Num.sqrt (5:R).
Proof.
move=>hUnit /critical_binary_all_direction_projection_locus hLocus.
have hAbs:`|u|^+2 + `|v|^+2= 1 by rewrite -!normrX !ger0_norm ?sqr_ge0.
have hu:=normr_ge0 u;have hv:=normr_ge0 v.
have hRoot:0<Num.sqrt (5:R) by rewrite sqrtr_gt0 ltr0n.
have hFive:0<(5:R) by rewrite ltr0n.
have hSquare:Num.sqrt (5:R)^+2= 5:=sqr_sqrtr (ltW hFive).
have hValue:0<3/Num.sqrt (5:R) by rewrite divr_gt0 // ltr0n.
have hValueSquare:(3/Num.sqrt (5:R))^+2= 9/5 by rewrite expr_div_n hSquare;field.
case:hLocus=>hEqual;nra.
Qed.
