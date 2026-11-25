(** Federer (1969), 3.4.2(8), p. 316: compare the
    cube-image diameter with the fine subdivision mesh. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_two_scale_diameter_bound]: the
    comparison with N*r/beta in 3.4.2(8), p. 316.
    The harmless positive padding by one also covers zero
    Lipschitz and flatness constants. This supporting bound
    retains the two subdivision scales and all zero-dimensional
    coordinate blocks. *)
Lemma critical_two_scale_diameter_bound (R:realType) (a b:nat)
    (h j eps D M lambda:R):
  0<=h ->0<=j ->0<=eps ->0<=D ->0<=M ->
  eps*real_power h lambda<=j ->
  (eps*D)*real_power (a%:R*h) lambda+M*b%:R*j<=
    (D*real_power a%:R lambda+M*b%:R+1)*j.
Proof.
move=>hh hj hEps hD hM hMesh.
have hPower:real_power (a%:R*h) lambda=
    real_power a%:R lambda*real_power h lambda.
  exact:real_power_product (ler0n R a) hh.
have hCoeff:0<=D*real_power a%:R lambda:=
  mulr_ge0 hD (real_power_nonnegative _ _).
have hScaled:=ler_wpM2l hCoeff hMesh.
have hExpand:(eps*D)*real_power (a%:R*h) lambda=
    (D*real_power a%:R lambda)*(eps*real_power h lambda).
  rewrite hPower;ring.
rewrite hExpand.
have hUpper: (D*real_power a%:R lambda+M*b%:R+1)*j=
    (D*real_power a%:R lambda)*j+M*b%:R*j+j by ring.
rewrite hUpper;lra.
Qed.
