(** Elementary finite order support for Federer (1969), 3.2.45,
    p. 280: choose one finite constant for all the degree ratios. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import FiniteRealEndpointBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_positive_power_majorant]: supporting the
    finite constant M in the cube-product estimate of Federer
    3.2.45, p. 280. Every finite real family is bounded by every
    positive natural power of one real M>1. The empty family is
    retained. This is an elementary helper, not a new source claim. *)
Lemma finite_positive_power_majorant (R : realType) (I : finType) (a : I -> R) :
  exists M : R, 1 < M /\ forall i r, (0 < r)%N -> a i <= M^+r.
Proof.
have [l [u [hlu hBounds]]] := finite_real_endpoint_bounds a a.
pose M : R := 2 + `|u|.
have hNorm : 0 <= `|u| := normr_ge0 u.
have hM : 1 < M by rewrite /M; lra.
have hUM : u <= M.
  have hAbs : u <= `|u| := ler_norm u.
  rewrite /M; lra.
exists M; split=> // i r hr.
apply: le_trans (hBounds i).2 (le_trans hUM _).
by rewrite -[X in X <= _]expr1 ler_eXn2l.
Qed.
