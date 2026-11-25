(** Federer (1969), 3.4.7, p. 325: the
    original coordinate powers have their actual ring-power
    germs. These supporting representative equations justify
    the finite transverse remainder module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_representative_power_exists]:
    the powers 1, xi, ..., xi^(k-1) used
    in 3.4.7, p. 325, have actual analytic
    representatives and their germs are the corresponding
    powers in the original opaque ring. *)
Theorem analytic_representative_power_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (f:@analytic_representative_type R X NX hNX a) i:
  exists g:@analytic_representative_type R X NX hNX a,
    (forall x,analytic_representative_value g x = (analytic_representative_value f x)^+i) /\
    (analytic_germ g:@analytic_germ_ring R X NX hNX a) =
      (analytic_germ f:@analytic_germ_ring R X NX hNX a)^+i.
Proof.
elim:i=>[|i [g [hValues hGerm]]].
- exists (@analytic_constant_representative R X NX hNX a 1);split.
  + move=>x;by rewrite expr0.
  + by rewrite expr0.
- exists (@analytic_multiply_representatives R X NX hNX a f g);split.
  + move=>x;change (analytic_representative_value f x*analytic_representative_value g x =
      (analytic_representative_value f x)^+i.+1).
    by rewrite hValues exprS.
  + rewrite -(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
    change ((analytic_germ f:@analytic_germ_ring R X NX hNX a)*analytic_germ g =
      (analytic_germ f:@analytic_germ_ring R X NX hNX a)^+i.+1).
    by rewrite hGerm exprS.
Qed.
