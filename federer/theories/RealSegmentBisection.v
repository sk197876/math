(** Supporting finite subdivision for Federer (1969), 2.10.7, pp. 174–175,
    proving H^1=L^1 on the line for the example in 2.5.10, p. 101. We use
    repeated bisection to avoid enumerating an arbitrary mesh. this
    bisection lemma is elementary infrastructure, not a separately numbered
    source claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_segment_half_nonnegative]: positive
    subdivision lengths supporting Federer 2.10.7,
    pp. 174–175; this is elementary real arithmetic. *)
Lemma real_segment_half_nonnegative (R : realType) (a b : R) :
  a<=b -> 0<=(b-a)/2.
Proof. by move=> hab; rewrite divr_ge0 ?subr_ge0 ?ler0n. Qed.

(** Source for [real_segment_half_sum]: additive lengths
    in the subdivision supporting Federer 2.10.7,
    pp. 174–175; no measure assertion is assumed. *)
Lemma real_segment_half_sum (R : realType) (a b : R) :
  (b-a)/2+(b-a)/2=b-a.
Proof. exact: esym (splitr (b-a)). Qed.

(** Source for [real_segment_midpoint_lengths]: equal
    half lengths and ordering for the subdivision argument
    in Federer 2.10.7, pp. 174–175. *)
Lemma real_segment_midpoint_lengths (R : realType) (a b : R) : a<=b ->
  let m := a+(b-a)/2 in
  a<=m /\ m<=b /\ m-a=(b-a)/2 /\ b-m=(b-a)/2.
Proof.
move=> hab /=; set h := (b-a)/2.
have hh : h+h=b-a := real_segment_half_sum a b.
have hp : 0<=h := real_segment_half_nonnegative hab.
have hleft : a+h-a=h by rewrite addrAC subrr add0r.
have hright : b-(a+h)=h by rewrite opprD addrA -hh addrK.
split; first by rewrite lerDl.
split; first by rewrite -subr_ge0 hright.
by split.
Qed.

(** Source for [real_segment_midpoint_cover]: two closed
    halves cover a segment, supporting the countable-cover
    estimates in Federer 2.10.7, pp. 174–175. *)
Lemma real_segment_midpoint_cover (R : realType) (a b m : R) :
  `[a,b] `<=` `[a,m] `|` `[m,b].
Proof.
move=> x; rewrite /= !in_itv /= => /andP[hax hxb].
case: (lerP x m)=> hxm.
- left; by rewrite hax.
- right; rewrite hxb andbT; exact: ltW hxm.
Qed.
