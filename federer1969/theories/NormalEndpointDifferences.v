(** Endpoint differences in Federer (1969), 2.10.32, pp. 196–197. Subtract
    the displayed normal-coordinate representations of a_i and b_i, and then
    the two corresponding original endpoint pairs. These supporting
    algebraic identities use the public normal decomposition laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import InnerProductUP OrthonormalFamilies UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [parallel_endpoint_difference]: supporting
    subtraction of the two normal-coordinate
    expressions in 2.10.32, p. 196.
    This identity is independent of dimension
    and of the existence of an inner product. *)
Lemma parallel_endpoint_difference (K : fieldType) (V : lmodType K)
    (p q u : V) (a b : K) :
  (p+a*:u)-(q+b*:u)=(p-q)+(a-b)*:u.
Proof. by rewrite opprD addrACA scalerBl. Qed.

(** Source for [normal_endpoint_difference]: direct
    identity a_i-b_i=(v_i-w_i)+
    (alpha_i-beta_i)u in 2.10.32,
    p. 196, with orthogonal feet substituted
    for v_i and w_i. *)
Lemma normal_endpoint_difference (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u x y : V) :
  x-y=(normal_foot hB u x-normal_foot hB u y)+
    (inner_coordinate hB u x-inner_coordinate hB u y)*:u.
Proof.
rewrite -parallel_endpoint_difference !normal_decomposition.
by [].
Qed.

(** Source for [doubled_parallel_endpoint_difference]: supporting
    scalar coefficients of the second original
    product in 2.10.32, p. 197. Its
    coefficient is gamma-delta plus twice
    alpha-beta, as printed. *)
Lemma doubled_parallel_endpoint_difference (K : fieldType) (V : lmodType K)
    (p q u : V) (a b g d : K) :
  (p+(g+2*a)*:u)-(q+(d+2*b)*:u)=
    (p-q)+((g-d)+2*(a-b))*:u.
Proof.
rewrite parallel_endpoint_difference; congr ((p-q)+_*:u); ring.
Qed.
