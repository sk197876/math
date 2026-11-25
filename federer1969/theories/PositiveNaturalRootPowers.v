(** Federer (1969), 3.2.42, printed p. 278:
    convert the integer-power expansion of the n-th roots
    into the printed fractional volume powers. All bases
    remain nonnegative, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerContinuity RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_natural_root_power]: supporting actual
    root-power cancellation in the first proof display of
    Federer 3.2.42, p. 278. Positive natural n ensures its
    real scalar exponent and reciprocal are positive. *)
Lemma positive_natural_root_power (R:realType) (a:R) n:
  0<=a ->(0<n)%N ->(real_power a (n%:R)^-1)^+n=a.
Proof.
move=>ha hn.
have hp:0<(n%:R:R) by rewrite ltr0n.
rewrite -(@real_power_natural_exponent R (real_power a (n%:R)^-1) n
  (real_power_nonnegative _ _)).
exact:real_power_inverse_power ha hp.
Qed.

(** Source for [positive_natural_root_subpower]: supporting
    (a^(1/n))^k=a^(k/n) in Federer 3.2.42, p. 278.
    The k=0 branch explicitly uses the project's integer
    power convention 0^0=1; the numbered corollary handles
    empty-source scope separately before applying its bound. *)
Lemma positive_natural_root_subpower (R:realType) (a:R) n k:
  0<=a ->(0<n)%N ->
  (real_power a (n%:R)^-1)^+k=real_power a (k%:R/n%:R).
Proof.
move=>ha hn.
have hp:0<(n%:R:R)^-1 by rewrite invr_gt0 ltr0n.
case:k=>[|k].
- by rewrite expr0 mul0r real_power_zero_exponent.
- have hk:0<(k.+1%:R:R) by rewrite ltr0n.
  rewrite -(@real_power_natural_exponent R (real_power a (n%:R)^-1) k.+1
    (real_power_nonnegative _ _)) (real_power_positive_iterate ha hp hk).
  by rewrite mulrC.
Qed.

(** Source for [positive_natural_power_root]: supporting the
    actual ball-volume root in Federer 3.2.42, p. 278.
    The positive natural power is undone on every nonnegative
    original radius, including radius zero. *)
Lemma positive_natural_power_root (R:realType) (a:R) n:
  0<=a ->(0<n)%N ->real_power (a^+n) (n%:R)^-1=a.
Proof.
move=>ha hn.
have hp:0<(n%:R:R) by rewrite ltr0n.
rewrite -(@real_power_natural_exponent R a n ha).
exact:real_power_root_cancel ha hp.
Qed.
