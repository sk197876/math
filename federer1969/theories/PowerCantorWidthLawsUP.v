(** Federer (1969), 3.3.21, p. 309: independently specified original scalar widths. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import ring.
From Federer Require Import RealPower CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_power_cantor_widths]: original common widths
    from the original Phi recursion, supporting 3.3.21, p. 309,
    as in 2.10.28, p. 193. No separation, density, measure or
    growth conclusion is a defining law. The widths remain local
    existential auxiliaries, not a globally selected field. *)
Record is_power_cantor_widths (R:realType) (c m:R) (n:nat->nat) (w:nat->R):Prop:={
  (** Source for [power_cantor_width_root]: the original root
      interval length is one, 3.3.21, p. 309. *)
  power_cantor_width_root:w 0%N= 1;
  (** Source for [power_cantor_width_positive]: original positive
      interval widths, before density is proved, 3.3.21, p. 309. *)
  power_cantor_width_positive:forall j,0<w j;
  (** Source for [power_cantor_width_split]: exactly the original
      Phi equal-cost split laws, 3.3.21, p. 309, from 2.10.28(4),
      p. 192. No externally imposed growth rate is included. *)
  power_cantor_width_split:forall j,is_cantor_split_radius
    (fun t=>c * real_power t m) (w j) (n j) (w j.+1)
}.
