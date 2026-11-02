(** Federer (1969), 2.10.29, p. 194, first paragraph: choose the next
    subdivision large enough to make its spacing arbitrarily small. The book
    uses the limit of (1-n^(-1/m))/(n-1). This supporting proof uses the
    stronger elementary bound t<d/(n-1), valid for every admitted concave
    gauge, and the existing Archimedean reciprocal estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cantor_split_spacing_small_exists]: supporting
    arbitrarily fine subdivision choice for the
    interleaved recursion in 2.10.29, p. 194.
    The split radius is used only through its
    sealed laws. The chosen natural subdivision
    number is a local existence witness. *)
Theorem cantor_split_spacing_small_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (d e : R) :
  0<d -> 0<e -> exists (n : nat) (s t : R),
    (2<=n)%N /\ is_cantor_split_radius h d n s /\
    t=cantor_split_spacing d n s /\ 0<t /\ t<e.
Proof.
move=> hd he.
have hediv : 0<e/d by rewrite divr_gt0.
have [k hk] := @positive_reciprocal_nat_small R (e/d) hediv.
pose n := k.+2.
have hn : (2<=n)%N by rewrite /n.
pose s := @cantor_split_radius R h hg d n hd hn.
have hs := @cantor_split_radius_specification R h hg d n hd hn.
pose t := cantor_split_spacing d n s.
have hst : s<t := cantor_split_spacing_strict hn hs.
have hspos := (cantor_split_radius_bounds hs).1.
change (is_true (0<s)) in hspos.
have htpos : 0<t := lt_trans hspos hst.
have hden : (0<n%:R-1 :> R) by rewrite subr_gt0 ltr1n.
have hdenEq : (n%:R-1 : R)=k.+1%:R by rewrite /n -!natr1; lra.
have hbound : d/(n%:R-1)<e.
  move: hk; by rewrite -hdenEq ltr_pdivlMr // mulrC.
have hdenInv : (0<(n%:R-1)^-1 :> R) by rewrite invr_gt0.
have htbound : t<d/(n%:R-1).
  rewrite /t /cantor_split_spacing (ltr_pM2r hdenInv); lra.
exists n,s,t; split=> //; split=> //; split=> //; split=> //.
exact: lt_trans htbound hbound.
Qed.
