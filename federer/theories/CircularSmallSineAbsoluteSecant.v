(** Federer (1969), 3.3.19, p. 306: unsigned
    local sine secants retain every ordering of original
    child indices in the final tangential packing. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import CircularTrigonometrySealed CircularSmallSineSecant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circular_small_sine_absolute_secant]: a
    local window has |sin(a)-sin(b)|>=kappa|a-b|
    for every 0<kappa<1, supporting the original
    tangential separation in the last claim of
    3.3.19, p. 306. Both index orders and equality
    follow from the proved signed secant theorem. *)
Theorem circular_small_sine_absolute_secant (R:realType) (kappa:R):
  0<kappa ->kappa<1 ->exists d:R,0<d /\forall a b:R,
    `|a|<=d ->`|b|<=d ->kappa*`|a-b|<=
    `|@CircularTrigonometry.sine R a-@CircularTrigonometry.sine R b|.
Proof.
move=>hk hk1.
have [d [hd hSecant]]:= @circular_small_sine_secant R kappa hk hk1.
exists d;split=>// a b ha hb.
case:(leP a b)=>hab.
- have h:= hSecant a b ha hb hab.
  have hWidth:0<=b-a by lra.
  have hProduct:= mulr_ge0 (ltW hk) hWidth.
  have hSin:0<=@CircularTrigonometry.sine R b-@CircularTrigonometry.sine R a by lra.
  have hFirst:`|a-b|= b-a by rewrite -[a-b]opprB normrN (ger0_norm hWidth).
  have hSecond:`|@CircularTrigonometry.sine R a-@CircularTrigonometry.sine R b|=
    @CircularTrigonometry.sine R b-@CircularTrigonometry.sine R a.
    by rewrite -[X in `|X|]opprB normrN (ger0_norm hSin).
  by rewrite hFirst hSecond.
- have h:= hSecant b a hb ha (ltW hab).
  have hWidth:0<=a-b by lra.
  have hProduct:= mulr_ge0 (ltW hk) hWidth.
  have hSin:0<=@CircularTrigonometry.sine R a-@CircularTrigonometry.sine R b by lra.
  by rewrite (ger0_norm hWidth) (ger0_norm hSin).
Qed.
