(** Federer (1969), 2.10.29, p. 194: derive positivity, shrinking lengths
    and the corrected interleaving from the scalar recurrence laws. Use
    Federer's erratum p. 4, book p. 194 line 8, for the final
    sigma_j>=t_(j+1)->0 assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import CantorSplitRadiusUP CantorSplitRadius CantorRadiusHalving
  InterleavedCantorScalesUP SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interleaved_cantor_widths_positive]: supporting
    positivity of all s_j,sigma_j in
    2.10.29, p. 194. It follows from
    the root and split laws, rather than
    being an extra defining assumption. *)
Lemma interleaved_cantor_widths_positive (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) : forall j,
  0<cantor_left_width D j /\ 0<cantor_right_width D j.
Proof.
move=> [|j].
- by rewrite (interleaved_cantor_left_root hD) (interleaved_cantor_right_root hD).
- split; [exact: (cantor_split_radius_bounds (interleaved_cantor_left_split hD j)).1 |
    exact: (cantor_split_radius_bounds (interleaved_cantor_right_split hD j)).1].
Qed.

(** Source for [interleaved_cantor_widths_geometric_bound]: supporting
    s_j,sigma_j<=2^-j in 2.10.29,
    p. 194. Both roots have width one,
    and every subdivision number is at least two. *)
Theorem interleaved_cantor_widths_geometric_bound (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) : forall j,
  cantor_left_width D j<=(2^-1)^+j /\ cantor_right_width D j<=(2^-1)^+j.
Proof.
have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
elim=> [|j [hl hr]].
- by rewrite (interleaved_cantor_left_root hD) (interleaved_cantor_right_root hD) expr0.
- have [hpl hpr] := @interleaved_cantor_widths_positive R h D hD j.
  have hL := (@cantor_radius_halving_bound R h _ _ _ hpl
    (interleaved_cantor_left_count hD j) (interleaved_cantor_left_split hD j)).1.
  have hR := (@cantor_radius_halving_bound R h _ _ _ hpr
    (interleaved_cantor_right_count hD j) (interleaved_cantor_right_split hD j)).1.
  rewrite exprSr; split.
  + exact (le_trans hL (ler_wpM2r hhalf0 hl)).
  + exact (le_trans hR (ler_wpM2r hhalf0 hr)).
Qed.

(** Source for [real_unit_interval_successor_power_bound]: supporting
    x^(j+1)<=x on [0,1], used to pass
    from the selected power-small spacings to
    the interleaving in 2.10.29, p. 194. *)
Lemma real_unit_interval_successor_power_bound (R : realType) (x : R) j :
  0<=x -> x<=1 -> x^+j.+1<=x.
Proof.
move=> hx hx1.
have hpow : x^+j<=x^+0.
  apply: ler_wiXn2l; [exact hx | exact hx1 | exact: leq0n].
rewrite expr0 in hpow.
have hh := ler_wpM2l hx hpow; by rewrite mulr1 -exprS in hh.
Qed.

(** Source for [interleaved_cantor_scales_interleaving]: direct
    sigma_(j-1)>=t_j>=s_j>=tau_j>=sigma_j
    >=t_(j+1) in 2.10.29, p. 194,
    including the corrected last term from
    erratum p. 4, book p. 194 line 8.
    Spacing indices are zero-based in the data. *)
Theorem interleaved_cantor_scales_interleaving (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) : forall j,
  cantor_left_spacing D j<=cantor_right_width D j /\
  cantor_left_width D j.+1<=cantor_left_spacing D j /\
  cantor_right_spacing D j<=cantor_left_width D j.+1 /\
  cantor_right_width D j.+1<=cantor_right_spacing D j /\
  cantor_left_spacing D j.+1<=cantor_right_width D j.+1.
Proof.
have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
have hhalf1 : (2^-1<=1 :> R) by rewrite invf_le1 ?ltr0n // ler1n.
have hunit j : cantor_left_width D j<=1 /\ cantor_right_width D j<=1.
  have [hl hr] := @interleaved_cantor_widths_geometric_bound R h D hD j.
  have hpow : (2^-1)^+j<=(2^-1)^+0 :> R.
    apply: ler_wiXn2l; [exact hhalf0 | exact hhalf1 | exact: leq0n].
  rewrite expr0 in hpow; split; [exact: le_trans hl hpow | exact: le_trans hr hpow].
have hleft j : cantor_left_spacing D j<=cantor_right_width D j.
  have [hlpos hrpos] := @interleaved_cantor_widths_positive R h D hD j.
  exact (le_trans (interleaved_cantor_left_small_spacing hD j)
    (@real_unit_interval_successor_power_bound R _ j (ltW hrpos) (hunit j).2)).
move=> j; split; first exact: hleft.
split.
- rewrite (interleaved_cantor_left_spacing_law hD j); apply: ltW.
  exact: cantor_split_spacing_strict (interleaved_cantor_left_count hD j) (interleaved_cantor_left_split hD j).
split.
- have [hlpos hrpos] := @interleaved_cantor_widths_positive R h D hD j.+1.
  exact (le_trans (interleaved_cantor_right_small_spacing hD j)
    (@real_unit_interval_successor_power_bound R _ j (ltW hlpos) (hunit j.+1).1)).
split; last exact: hleft.
rewrite (interleaved_cantor_right_spacing_law hD j); apply: ltW.
exact: cantor_split_spacing_strict (interleaved_cantor_right_count hD j) (interleaved_cantor_right_split hD j).
Qed.

(** Source for [interleaved_cantor_spacings_tend_to_zero]: direct
    convergence to zero at the end of the
    interleaving in 2.10.29, p. 194,
    corrected by erratum p. 4, book p. 194
    line 8. Both spacing sequences tend to
    zero; their strict positivity follows from
    the split laws, without assuming convergence
    as part of the scale specification. *)
Theorem interleaved_cantor_spacings_tend_to_zero (R : realType) (h : R -> R) D
    (hD : is_interleaved_cantor_scales h D) :
  forall e : R, 0<e -> exists N, forall j, (N<=j)%N ->
    (0<cantor_left_spacing D j /\ cantor_left_spacing D j<e) /\
    (0<cantor_right_spacing D j /\ cantor_right_spacing D j<e).
Proof.
move=> e he; have [N hN] := @sequence_inverse_power_small R e he.
have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
have hhalf1 : (2^-1<=1 :> R) by rewrite invf_le1 ?ltr0n // ler1n.
have hsmall j : (N<=j)%N -> (2^-1)^+j<e.
  move=> hNj; apply: le_lt_trans _ hN.
  apply: ler_wiXn2l; [exact hhalf0 | exact hhalf1 | exact hNj].
exists N=> j hNj.
have [hlw hrw] := @interleaved_cantor_widths_geometric_bound R h D hD j.
have [hlwn hrwn] := @interleaved_cantor_widths_geometric_bound R h D hD j.+1.
have [hlt [hls [hrt [hrs hnext]]]] := @interleaved_cantor_scales_interleaving R h D hD j.
have [hlpos hrpos] := @interleaved_cantor_widths_positive R h D hD j.+1.
have hNjnext : (N<=j.+1)%N := leq_trans hNj (leqnSn j).
split; split.
- exact: lt_le_trans hlpos hls.
- exact: le_lt_trans hlt (le_lt_trans hrw (hsmall j hNj)).
- exact: lt_le_trans hrpos hrs.
- exact: le_lt_trans hrt (le_lt_trans hlwn (hsmall j.+1 hNjnext)).
Qed.
