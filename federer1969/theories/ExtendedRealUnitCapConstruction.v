(** Private scalar existence witness supporting the finite
    metric carrier for Federer (1969), 3.2.46, p. 281.
    Downstream arguments use only the independent cap laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealUnitCapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [extended_real_unit_cap_exists]: technical
    existence proof for the finite carrier of 3.2.46, p. 281;
    the displayed cap is subsequently hidden by a seal. *)
Lemma extended_real_unit_cap_exists (R : realType) :
  exists cap : \bar R -> R, is_extended_real_unit_cap cap.
Proof.
exists (fun z=>match z with EFin r=>Order.min r 1 | EPInf=>1 | ENInf=>0 end).
by constructor.
Qed.
