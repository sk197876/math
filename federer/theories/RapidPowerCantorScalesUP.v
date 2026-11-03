(** Federer (1969), 3.2.40, p. 276: independent scalar
    recurrence laws for a sufficiently rapid subdivision choice
    in the actual same-factor Cantor-square example. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_rapid_power_cantor_scales]: supporting quantitative
    choice of the schedule n in Federer 3.2.40, p. 276. The
    widths start at one and obey the original equal-cost split
    laws from 2.10.28, pp. 192--193. The last condition selects
    sufficiently large subdivisions before any geometric or
    Minkowski-content conclusion is proved. Merely diverging
    schedules are not all asserted to give the desired example. *)
Record is_rapid_power_cantor_scales (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R):Prop:={
  (** Source for [rapid_power_cantor_root]: the original unit
      parent in 2.10.28, p. 193, used by 3.2.40, p. 276. *)
  rapid_power_cantor_root:s 0%N= 1;
  (** Source for [rapid_power_cantor_count]: supporting increasing
      lower bound on the subdivision numbers of 3.2.40, p. 276.
      Divergence and the required n_j>=2 follow from this law. *)
  rapid_power_cantor_count:forall j,(j.+2<=n j)%N;
  (** Source for [rapid_power_cantor_split]: original equal-cost
      split in 2.10.28(4), p. 192, at each stage of the
      example in 3.2.40, p. 276. *)
  rapid_power_cantor_split:forall j,is_cantor_split_radius
    (fun t=>c*real_power t m) (s j) (n j) (s j.+1);
  (** Source for [rapid_power_cantor_growth]: supporting sufficiently
      rapid choice in 3.2.40, p. 276. This is a scalar
      subdivision bound; no tube or content value is a law. *)
  rapid_power_cantor_growth:forall j,j.+1%:R<=(n j)%:R*real_power (s j) (1-2 * m)
}.
