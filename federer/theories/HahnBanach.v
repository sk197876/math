(** Federer (1969), 1.10.5, p. 48: supporting functional extension used in
    the norm duality proof. This public interface exposes the finite-valued
    Hahn-Banach statement of 2.4.12, p. 86, using only the sealed existence
    laws. No finite-dimensional hypothesis is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialLinearMap HahnBanachSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_hahn_banach]: Federer 1.10.5,
    p. 48, supporting Hahn-Banach theorem from 2.4.12, p. 86.
    A partially defined linear scalar functional dominated by a
    finite-valued seminorm extends to a dominated total linear functional. *)
Theorem seminorm_hahn_banach (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) :
  exists f : {linear V -> R^o},
    (forall x a, G x a -> f x=a) /\ forall x, f x<=N x.
Proof.
exists (@HahnBanach.extension R V N hN G hG hdom); split.
- exact: HahnBanach.agreement.
- exact: HahnBanach.bound.
Qed.
