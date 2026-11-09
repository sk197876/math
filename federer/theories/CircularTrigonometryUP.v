(** Federer (1969), 3.3.19, p. 302: independent elementary
    circular trigonometry for the printed exp(2 pi i k/n).
    These are scalar background laws; no disc separation,
    counting, covering or density conclusion is a field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealTrigonometryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_circular_trigonometry]: elementary scalar
    laws supporting the actual circular disc centres of
    3.3.19, p. 302, before any geometric estimates. *)
Record is_circular_trigonometry (R:realType) (S C A D:R->R) (p:R):Prop:={
  (** Source for [circular_trig_basic]: the original scalar trigonometric laws, with actual derivatives, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_basic:is_real_trigonometric_system S C A p;
  (** Source for [circular_trig_unit]: unit-circle identity, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_unit:forall x,C x^+2+S x^+2= 1;
  (** Source for [circular_trig_sine_add]: sine addition, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_sine_add:forall x y,S (x+y)=S x*C y+C x*S y;
  (** Source for [circular_trig_cosine_add]: cosine addition, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_cosine_add:forall x y,C (x+y)=C x*C y-S x*S y;
  (** Source for [circular_trig_cosine_even]: even cosine, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_cosine_even:forall x,C (-x)=C x;
  (** Source for [circular_trig_sine_pi]: sine at the half-period, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_sine_pi:S p= 0;
  (** Source for [circular_trig_cosine_pi]: cosine at the half-period, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_cosine_pi:C p= -1;
  (** Source for [circular_trig_sine_positive]: positive upper-semicircle sine, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_sine_positive:forall x,0<x ->x<p ->0<S x;
  (** Source for [circular_trig_cosine_decreases]: strict cosine decrease on the upper semicircle, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_cosine_decreases:forall x y,0<=x ->x<=p ->0<=y ->y<=p ->x<y ->C y<C x;
  (** Source for [circular_trig_acos_range]: the inverse cosine range, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_acos_range:forall y,-1<=y ->y<= 1 ->0<=D y /\ D y<=p;
  (** Source for [circular_trig_acos_cosine]: the inverse cosine equation, scalar background for
      the original disc centres in 3.3.19, p. 302. *)
  circular_trig_acos_cosine:forall y,-1<=y ->y<= 1 ->C (D y)=y
}.
