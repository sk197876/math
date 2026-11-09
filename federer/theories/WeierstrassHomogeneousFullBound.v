(** Federer (1969), 3.4.6, p. 323: the
    original homogeneous coefficient norm bounds all transverse
    values by the corresponding power of the original norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP HomogeneousPolynomialFunctions PolynomialNorm PolynomialFiniteNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_homogeneous_full_bound]: the
    actual degree-j polynomial bound on the unit ball
    scales to every original z, supporting the absolute
    double-series estimate of 3.4.6, p. 323.
    Zero degree, zero z and arbitrary source dimension
    are retained without a unit-vector existence premise. *)
Theorem weierstrass_homogeneous_full_bound (R:realType) (K:lmodType R)
    (NK:K->R) (hNK:is_real_norm NK) j (P:K->R) (A:R):
  @is_homogeneous_polynomial R K R^o j P ->
  (forall z,NK z<=1 ->`|P z|<=A) ->forall z,`|P z|<=NK z^+j*A.
Proof.
move=>hP hBound z.
have hNorm:(polynomial_norm hNK.1 (fun r:R^o=>(`|r|)%R) P<=A%:E)%E.
  apply:(polynomial_norm_bound hNK.1 (fun r:R^o=>`|r|) P _).2.
  exact:hBound.
exact:(@homogeneous_polynomial_finite_norm_bound R K R^o NK (fun r=>`|r|)
  hNK (@scalar_absolute_value_norm R).1 j P hP A hNorm z).
Qed.
