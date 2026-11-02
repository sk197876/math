(** Federer (1969), 3.2.3, p. 243: let lambda
    decrease to one in the multiplicative area bounds.
    The existing abstract scalar power and geometric squeeze
    give the result also for zero and infinite integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedGeometricSqueeze
  RealPower RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_power_geometric_squeeze]: the
    inference by lambda approaching one in Federer 3.2.3,
    p. 243. Every fixed natural power of lambda gives
    a coinitial family of factors above one, including the
    zero power as the exact factor one. *)
Lemma extended_power_geometric_squeeze (R:realType) (L U : \bar R) k:
  0<=L -> (forall lambda:R,(1<lambda)%R -> U<=(lambda^+k)%R%:E*L) -> U<=L.
Proof.
move=>hL hU; case:k hU=>[hU|k hU].
- have hh:=hU 2%R (ltr1n _ 2); by rewrite expr0 mul1e in hh.
- apply:(@extended_geometric_squeeze R L U hL)=>t ht.
  have ht0:(0<t)%R:=lt_trans ltr01 ht.
  have hk:(0<(k.+1%:R:R))%R by rewrite ltr0n.
  have hki:(0<(k.+1%:R:R)^-1)%R by rewrite invr_gt0.
  pose lambda:=real_power t (k.+1%:R:R)^-1.
  have hLam:(1<lambda)%R.
    have hh:=real_power_strict_monotone ler01 ht hki.
    by rewrite real_power_one_base in hh.
  have hLam0:(0<lambda)%R:=lt_trans ltr01 hLam.
  have hPower:(lambda^+k.+1)%R=t.
    rewrite -(real_power_natural_exponent k.+1 (ltW hLam0)).
    rewrite /lambda (@real_power_positive_iterate R t (k.+1%:R:R)^-1 (k.+1%:R:R)
      (ltW ht0) hki hk).
    rewrite mulVf ?gt_eqF //.
    exact (real_power_one_exponent (ltW ht0)).
  by have hh:=hU lambda hLam; rewrite hPower in hh.
Qed.
