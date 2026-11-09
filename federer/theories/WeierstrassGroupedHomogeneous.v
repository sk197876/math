(** Federer (1969), 3.4.6, p. 323: the actual
    double series is grouped by total homogeneous degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousPolynomialFunctions WeierstrassHomogeneousArithmetic WeierstrassLinearPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_grouped_homogeneous]: the
    finite sum of xi(x)^i Q_(i,m-i)(eta(x)) is an
    actual homogeneous polynomial of total degree m,
    3.4.6, p. 323. Original bounded maps
    may later supply continuity; the algebraic assertion
    requires only their linearity. *)
Theorem weierstrass_grouped_homogeneous (R:realType) (X K:lmodType R)
    (xi:Hom X R^o) (projection:Hom X K) (q:nat->nat->K->R) m:
  (forall i j,@is_homogeneous_polynomial R K R^o j (q i j)) ->
  @is_homogeneous_polynomial R X R^o m
    (fun x=>\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)).
Proof.
move=>hQ.
apply:(@weierstrass_homogeneous_sum R X m (Finite.clone 'I_m.+1 _))=>i.
have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
have hPower:=@weierstrass_functional_power_homogeneous R X xi i.
have hPullback:=@weierstrass_homogeneous_pullback R X K projection (m-i)%N
  (q i (m-i)%N) (hQ i (m-i)%N).
have hProduct:=@weierstrass_homogeneous_multiply R X i (m-i)%N
  (fun x=>(xi x)^+i) (fun x=>q i (m-i)%N (projection x)) hPower hPullback.
by rewrite subnKC // in hProduct.
Qed.
