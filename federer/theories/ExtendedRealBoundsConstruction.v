(** Federer (1969), 2.1.1, p. 51: every extended-real set has a supremum and
    an infimum, including the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedSupremumUP ExtendedSupremumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_supremum_exists]: Federer 2.1.1,
    p. 51, third paragraph; existence proof from real completeness.
    If positive infinity occurs it is the supremum. Otherwise apply
    the real-value supremum already constructed in 1.10.5, unless
    there are no finite values, when the supremum is negative infinity. *)
Theorem extended_real_supremum_exists (R : realType) (S : set (\bar R)) :
  exists c, is_extended_real_supremum S c.
Proof.
have [hy|hy] := pselect (S +oo).
- exists +oo; constructor; first by move=> x _; exact: leey.
  by move=> d hu; exact: hu.
- pose F : set R := fun r => S r%:E.
  have [hn|hn] := pselect (F !=set0).
  + exists (ExtendedSupremum.value hn); constructor.
    * move=> [r| |] hr.
      -- exact: (extended_supremum_upper (ExtendedSupremum.laws hn) hr).
      -- by exfalso; exact: hy.
      -- exact: leNye.
    * move=> d hu; apply: (extended_supremum_least (ExtendedSupremum.laws hn)).
      by move=> r hr; exact: hu.
  + exists -oo; constructor.
    * move=> [r| |] hr; last exact: lexx.
      -- exfalso; apply: hn; by exists r.
      -- by exfalso; exact: hy.
    * by move=> d _; exact: leNye.
Qed.
