(** Federer (1969), 2.10.29, p. 194: choose a sufficiently late interval
    between consecutive t_j, with small width powers and 1/j exponent error.
    These are consequences of the interleaved scalar laws, including the
    corrected convergence in Federer's erratum p. 4, book p. 194 line 8. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InterleavedCantorScalesUP InterleavedCantorScalesLaws
  RealPower RealPowerContinuity SequencePowerBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interleaved_cantor_spacing_successor_bound]: supporting
    t_(j+1)<=t_j in 2.10.29, p. 194,
    following the full corrected interleaving chain. *)
Lemma interleaved_cantor_spacing_successor_bound (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) j :
  cantor_left_spacing D j.+1<=cantor_left_spacing D j.
Proof.
have [hlt [hls [hrt [hrs hnext]]]] := interleaved_cantor_scales_interleaving hD j.
exact (le_trans hnext (le_trans hrs (le_trans hrt hls))).
Qed.

(** Source for [interleaved_cantor_spacing_band]: direct
    choice t_j>=d>=t_(j+1) in 2.10.29,
    p. 194, beyond any prescribed index.
    Shared band endpoints are retained. *)
Lemma interleaved_cantor_spacing_band (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) N (d : R) :
  0<d -> d<=cantor_left_spacing D N ->
  exists j, (N<=j)%N /\ d<=cantor_left_spacing D j /\ cantor_left_spacing D j.+1<=d.
Proof.
move=> hd hstart.
have [K hK] := interleaved_cantor_spacings_tend_to_zero hD hd.
have hex : exists k, cantor_left_spacing D (N+k).+1<=d.
  have hKN : (K<=(N+K).+1)%N := leq_trans (leq_addl N K) (leqnSn (N+K)).
  exists K; exact: ltW (hK (N+K).+1 hKN).1.2.
have [k hk hmin] := ex_minnP hex.
exists (N+k)%N; split; first exact: leq_addr.
split; last exact hk.
case: k hk hmin=> [|k] hk hmin; first by rewrite addn0.
rewrite leNgt; apply/negP=> hbad.
have hprev : cantor_left_spacing D (N+k).+1<=d.
  apply: ltW; by rewrite addnS in hbad.
have hb := hmin k hprev; by rewrite leqNgt ltnSn in hb.
Qed.

(** Source for [interleaved_cantor_width_powers_small]: supporting
    eventual smallness of s_j^m and sigma_j^m
    in 2.10.29, p. 194. It follows
    from the proved geometric width bounds,
    for every positive real exponent. *)
Lemma interleaved_cantor_width_powers_small (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) (m e : R) :
  0<m -> 0<e -> exists N, forall j, (N<=j)%N ->
    real_power (cantor_left_width D j) m<=e /\ real_power (cantor_right_width D j) m<=e.
Proof.
move=> hm he.
have hroot : 0<real_power e m^-1 := real_power_strictly_positive _ he.
have [N hN] := sequence_inverse_power_small hroot.
have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
have hhalf1 : (2^-1<=1 :> R) by rewrite invf_le1 ?ltr0n // ler1n.
exists N=> j hNj.
have hgeo := ler_wiXn2l hhalf0 hhalf1 hNj.
have [hl hr] := interleaved_cantor_widths_geometric_bound hD j.
have [hl0 hr0] := interleaved_cantor_widths_positive hD j.
have hb x : 0<=x -> x<=(2^-1)^+j -> real_power x m<=e.
  move=> hx hxb; rewrite -(real_power_inverse_power (ltW he) hm).
  exact (real_power_monotone hx (ltW (le_lt_trans (le_trans hxb hgeo) hN)) hm).
split; [exact: hb (ltW hl0) hl | exact: hb (ltW hr0) hr].
Qed.

(** Source for [reciprocal_index_exponent_error_small]: supporting
    eventual k+1/j<=m+1 in 2.10.29,
    p. 194, using only the positive gap
    between k and m+1. *)
Lemma reciprocal_index_exponent_error_small (R : realType) (m k : R) :
  k<m+1 -> exists N, forall j, (N<=j)%N -> k+(j.+1%:R)^-1<=m+1.
Proof.
move=> hgap.
have hpos : 0<m+1-k by rewrite subr_gt0.
have [N hN] := positive_reciprocal_nat_small hpos.
exists N=> j hNj.
have hJ : (0<j.+1%:R :> R) by rewrite ltr0n.
have hNN : (0<N.+1%:R :> R) by rewrite ltr0n.
have hcast : (N.+1%:R<=j.+1%:R :> R) by rewrite ler_nat.
have hi := (@lef_pV2 R (j.+1%:R) (N.+1%:R) hJ hNN).
have hji : (j.+1%:R : R)^-1<=(N.+1%:R : R)^-1 by rewrite hi.
have hh := ltW (le_lt_trans hji hN).
by move: hh; rewrite lerBrDl.
Qed.
