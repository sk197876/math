(** Federer (1969), 3.1.13, p. 225:
    G_i is exactly sup im ||D^i mu||,
    not an arbitrary upper bound. Existence
    follows from compact support, and the supremum
    implementation remains behind an opaque interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm
  HilbertFormCompactness LinearBasis ContinuousMultilinearUP ContinuousMultilinearNorm
  NormHigherDifferentialUP InnerSmoothUnitBump UniformFunctionNormUP BoundedFunctionNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_bump_derivative_supremum_exists]:
    the exact finite constants G_i in
    Federer 3.1.13, p. 225.
    The supremum may be zero, including
    the positive-order derivatives in dimension zero. *)
Theorem inner_bump_derivative_supremum_exists (R : realType)
    (X : lmodType R) (B : X->X->R) (hB : is_inner_product B)
    n (e : 'I_n->X) (he : is_basis e)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (inner_norm hB)
      (fun t : R^o=>`|t|) (@ev i) (@ZN i)) k :
  exists (D : X->Z k) (G : R),
    (forall x, has_norm_higher_differential (inner_norm hB) ev ZN
      (fun _=>True) (inner_smooth_unit_bump hB) k x (D x)) /\
    is_uniform_function_norm (fun x=>@ZN k (D x)) G /\
    forall x, 2<inner_norm hB x -> D x=0.
Proof.
have [D [C [hD [hC [hb hz]]]]] :=
  inner_smooth_unit_bump_derivative_bounds he hZ k.
have hNk := continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R) (@hZ k).
have hbound : exists M : R, 0<=M /\ forall x, `|@ZN k (D x)|<=M.
  exists C; split; first exact: (ltW hC).
  move=>x; rewrite (ger0_norm (real_seminorm_nonnegative hNk.1 (D x))).
  exact: hb.
exists D, (BoundedFunctionNorm.value hbound).
split; first exact hD; split; last exact hz.
exact: BoundedFunctionNorm.laws.
Qed.
