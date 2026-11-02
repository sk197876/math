(** Federer (1969), 2.10.47, p. 204: choose j with
    2^(-j-1)<=diam(S)<=2^(-j). These scalar bounds also show that the grid
    cutoffs tend to zero. They are proved from natural powers and the real
    Archimedean property, without importing logarithms. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GeometricPowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dyadic_side_positive]: positivity of each
    side 2^(-j) in 2.10.47, p. 204. *)
Lemma dyadic_side_positive (R : realType) j : (0 : R)<((2^j)%N)%:R^-1.
Proof. by rewrite invr_gt0 ltr0n expn_gt0. Qed.

(** Source for [dyadic_side_antitone]: supporting monotonicity
    of the cube sides in 2.10.47, p. 204. *)
Lemma dyadic_side_antitone (R : realType) i j : (i<=j)%N ->
  (((2^j)%N)%:R^-1 : R)<=((2^i)%N)%:R^-1.
Proof.
move=> hij.
have hi0 : (0 : R)<((2^i)%N)%:R by rewrite ltr0n expn_gt0.
have hj0 : (0 : R)<((2^j)%N)%:R by rewrite ltr0n expn_gt0.
by rewrite (@lef_pV2 R _ _ hj0 hi0) ler_nat leq_exp2l.
Qed.

(** Source for [dyadic_side_successor]: halving of the side
    at each subdivision in 2.10.47, p. 204. *)
Lemma dyadic_side_successor (R : realType) j :
  (((2^j.+1)%N)%:R^-1 : R)=((2^j)%N)%:R^-1/2.
Proof. by rewrite expnSr natrM invfM. Qed.

(** Source for [dyadic_sides_arbitrarily_small]: cutoffs tend
    to zero in the two comparisons and final limit
    of 2.10.47, pp. 204–205. *)
Lemma dyadic_sides_arbitrarily_small (R : realType) (d : R) : 0<d ->
  exists j, ((2^j)%N)%:R^-1<d.
Proof.
move=> hd.
have htwo : (1 : R)<2 by rewrite ltr1n.
have [j hj] := @geometric_powers_unbounded R 2 d^-1 htwo.
have hp : (0 : R)<2^+j by rewrite exprn_gt0 // ltr0n.
have hdi : 0<d^-1 by rewrite invr_gt0.
exists j; by rewrite natrX -[d]invrK (@ltf_pV2 R _ _ hp hdi).
Qed.

(** Source for [dyadic_scale_bracket]: the displayed scale
    choice in 2.10.47, p. 204, strengthened to
    a strict lower bound. If d is below the i-th
    side, the chosen level j is at least i. *)
Theorem dyadic_scale_bracket (R : realType) i (d : R) :
  0<d -> d<=((2^i)%N)%:R^-1 ->
  exists j, [/\ (i<=j)%N, ((2^j.+1)%N)%:R^-1<d & d<=((2^j)%N)%:R^-1].
Proof.
move=> hd hi.
have [N hN hmin] := ex_minnP (dyadic_sides_arbitrarily_small hd).
have hiN : (i<N)%N.
  rewrite ltnNge; apply/negP=> hNi.
  have hh := le_lt_trans (le_trans hi (@dyadic_side_antitone R N i hNi)) hN.
  by rewrite ltxx in hh.
have hN0 : (0<N)%N := leq_ltn_trans (leq0n i) hiN.
exists N.-1; split.
- by rewrite -(ltnS i N.-1) (prednK hN0).
- by rewrite (prednK hN0).
- rewrite leNgt; apply/negP=> hbad.
  have hh := hmin N.-1 hbad.
  have hlt : (N.-1<N)%N by rewrite -(prednK hN0) ltnSn.
  have hn := leq_ltn_trans hh hlt; by rewrite ltnn in hn.
Qed.
