(** Federer (1969), 3.2.33, p. 270: independent
    laws for the printed series psi and its smooth positive set. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormRegularity RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_interval_bump_series]: the displayed series
    defining psi in Federer 3.2.33, p. 270, and its
    smoothness and exact positive set. Zero-based index j uses
    the printed positive exponent j+1. The limit is uniform
    on the whole real line. A unit bound follows from the
    chosen half-length intervals and unit-normalized bump. *)
Record is_interval_bump_series (R:realType) (a b:nat->R) (phi psi:R->R):Prop:={
  (** Source for [interval_bump_series_limit]: the actual printed
      series defining psi in Federer 3.2.33, p. 270. *)
  interval_bump_series_limit:forall e:R,0<e ->exists N:nat,forall M,(N<=M)%N ->forall t,
    `|(\sum_(j<M) (b j-a j)^+j.+1*phi ((t-a j)/(b j-a j)))-psi t|<e;
  (** Source for [interval_bump_series_bounds]: supporting nonnegative
      and finite bound for psi in Federer 3.2.33, p. 270. *)
  interval_bump_series_bounds:forall t,0<=psi t<= 1;
  (** Source for [interval_bump_series_positive]: psi is positive
      exactly on V, supporting {g'= 0}= T minus V in
      Federer 3.2.33, p. 270. *)
  interval_bump_series_positive:forall t,
    (0<psi t <->(\bigcup_j real_open_interval (a j) (b j)) t);
  (** Source for [interval_bump_series_smooth]: psi is of class
      infinity, Federer 3.2.33, p. 270, with actual higher differentials. *)
  interval_bump_series_smooth:norm_class_all_orders (scalar_absolute_value_norm R)
    (scalar_absolute_value_norm R) (fun _=>True) psi
}.
