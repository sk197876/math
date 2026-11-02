(** Federer (1969), 3.1.13, p. 224:
    the smooth radial cutoff in Euclidean space
    and finite bounds for each of its derivatives.
    The same argument works in a finite-dimensional
    space with a specified inner product. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness LinearBasis FiniteNormMetricCompactness
  ContinuousMultilinearUP NormHigherDifferentialUP NormClassHigherUP
  NormUnitBumpUP NormUnitBumpSealed NormCompactSupportHigherBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_product_squared_norm_specification]:
    the squared Euclidean norm is a continuous
    quadratic form, supporting mu in Federer
    3.1.13, p. 224. The
    Cauchy inequality is the already proved
    Chapter 1 bound for the supplied inner product. *)
Lemma inner_product_squared_norm_specification (R : realType)
    (X : lmodType R) (B : X->X->R) (hB : is_inner_product B) :
  norm_squared_bilinear_form (inner_norm hB) B.
Proof.
split.
- split; first exact: (inner_bilinear hB).
  exists 1; split; first exact: ler01.
  move=>x y; rewrite mul1r; exact: (inner_cauchy hB x y).
- move=>x; exact: (esym (inner_norm_sqr hB x)).
Qed.

(** Source for [inner_smooth_unit_bump]:
    the radial cutoff mu on Federer
    3.1.13, p. 224, exposed
    through the sealed abstract bump interface.
    Its particular squared-norm construction is private. *)
Definition inner_smooth_unit_bump (R : realType)
    (X : lmodType R) (B : X->X->R) (hB : is_inner_product B) : X->R :=
  @NormUnitBump.value R X (inner_norm hB) B
    (inner_norm_real_norm hB) (inner_product_squared_norm_specification hB).

(** Source for [inner_smooth_unit_bump_laws]:
    the bump is radial, takes values
    in [0,1], is one at norm
    at most one, and zero at norm
    at least two, Federer 3.1.13, p. 224. *)
Theorem inner_smooth_unit_bump_laws (R : realType)
    (X : lmodType R) (B : X->X->R) (hB : is_inner_product B) :
  is_norm_unit_bump (inner_norm hB) (inner_smooth_unit_bump hB).
Proof. exact: NormUnitBump.laws. Qed.

(** Source for [inner_smooth_unit_bump_derivative_bounds]:
    finite constants G_i bound the actual
    derivatives of mu everywhere, Federer 3.1.13,
    p. 224. Compactness is used
    only for the closed radius-two ball;
    outside it locality makes every derivative zero.
    The finite basis may have cardinality zero. *)
Theorem inner_smooth_unit_bump_derivative_bounds (R : realType)
    (X : lmodType R) (B : X->X->R) (hB : is_inner_product B)
    n (e : 'I_n->X) (he : is_basis e)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (inner_norm hB)
      (fun t : R^o=>`|t|) (@ez i) (@ZN i)) k :
  exists (D : X->Z k) (G : R),
    (forall x, has_norm_higher_differential (inner_norm hB) ez ZN
      (fun _=>True) (inner_smooth_unit_bump hB) k x (D x)) /\
    0<G /\ (forall x, @ZN k (D x)<=G) /\
    forall x, 2<inner_norm hB x -> D x=0.
Proof.
pose hN := inner_norm_real_norm hB.
have hmu := inner_smooth_unit_bump_laws hB.
have hc := @NormUnitBump.smooth R X (inner_norm hB) B hN
  (inner_product_squared_norm_specification hB) Z ez ZN hZ k.
pose K := [set x : X | inner_norm hB x<=2].
have hK := @finite_norm_metric_ball_compact R X (inner_norm hB) hN n e he 2.
have hz x (hx : ~K x) : inner_smooth_unit_bump hB x=0.
  apply: (norm_unit_bump_outer hmu); apply: ltW.
  rewrite ltNge; apply/negP=>hle; exact: (hx hle).
have [D [G [hD [hG [hbound hzero]]]]] :=
  @norm_compact_support_higher_differential_bound R X R^o (inner_norm hB)
    (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R)
    Z ez ZN hZ K (inner_smooth_unit_bump hB) k hK hz hc.
exists D, G; split; first exact hD.
split; first exact hG.
split; first exact hbound.
move=>x hx; apply: hzero=>h; by move:hx; rewrite ltNge h.
Qed.
