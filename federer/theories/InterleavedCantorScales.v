(** Federer (1969), 2.10.29, p. 194: public interleaved subdivision
    sequences and the power-gauge length formulas derived from their
    abstract split laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ConcaveIntervalGaugeUP RealPower PowerCantorSplit
  InterleavedCantorScalesUP InterleavedCantorScalesLaws InterleavedCantorScalesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interleaved_cantor_scales]: direct
    selected interleaved sequences in 2.10.29,
    p. 194, through their proved opaque
    root, split and small-spacing specification. *)
Definition interleaved_cantor_scales (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) := @InterleavedCantorScales.value R h hg.

(** Source for [interleaved_cantor_scales_specification]: direct
    abstract recurrence laws for the chosen
    sequences in 2.10.29, p. 194.
    Downstream proofs do not unfold a recursive
    or scalar-selection implementation. *)
Lemma interleaved_cantor_scales_specification (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) :
  is_interleaved_cantor_scales h (@interleaved_cantor_scales R h hg).
Proof. exact: InterleavedCantorScales.laws. Qed.

(** Source for [interleaved_power_cantor_length_formulas]: direct
    s_j=s_(j-1)*n_j^(-1/m) and
    sigma_j=sigma_(j-1)*nu_j^(-1/m)
    in 2.10.29, p. 194. Both formulas
    follow from the defining equal-cost laws;
    the positive normalising constant cancels. *)
Theorem interleaved_power_cantor_length_formulas (R : realType) (c m : R) D :
  0<c -> 0<m -> is_interleaved_cantor_scales (fun t=>c*real_power t m) D ->
  forall j,
    cantor_left_width D j.+1=cantor_left_width D j*
      real_power (cantor_left_subdivision D j)%:R (-m^-1) /\
    cantor_right_width D j.+1=cantor_right_width D j*
      real_power (cantor_right_subdivision D j)%:R (-m^-1).
Proof.
move=> hc hm hD j.
have [hlpos hrpos] := @interleaved_cantor_widths_positive R _ D hD j.
split.
- exact: (@power_cantor_split_length R c m _ _ _ hc hm hlpos
    (interleaved_cantor_left_count hD j) (interleaved_cantor_left_split hD j)).
- exact: (@power_cantor_split_length R c m _ _ _ hc hm hrpos
    (interleaved_cantor_right_count hD j) (interleaved_cantor_right_split hD j)).
Qed.
