(** Federer (1969), 1.7.6, p. 33: symmetry, skew signs, orthogonal
    injections and orthogonal projections under exterior powers. The
    statements use the abstract adjoint and projection specifications and
    allow arbitrary ambient dimension whenever the required adjoint already
    exists. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  InnerExteriorNaturality ExteriorAdjoint ExteriorMapScaling AdjointUP
  AdjointLaws AdjointCriteria SymmetricEndomorphisms OrthogonalMaps
  ExteriorGrading ExteriorMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_power_symmetric]: Federer 1.7.6,
    p. 33, an exterior power of a symmetric endomorphism is symmetric. *)
Theorem exterior_power_symmetric (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) : is_symmetric_endomorphism B f -> forall m,
  is_symmetric_endomorphism (@exterior_inner_form R h2 V B hB m) (exterior_power_map f m).
Proof.
move=> hf m x y; symmetry.
exact (@exterior_power_adjoint R h2 V V B B hB hB f f
  (symmetric_self_adjoint hf) m x y).
Qed.

(** Source for [exterior_power_skew_adjoint_sign]: Federer 1.7.6,
    p. 33, if f is skewsymmetric, the m-th exterior map of its
    adjoint is (-1)^m times the m-th exterior map of f. Together
    with exterior_power_adjoint this is the printed star identity. *)
Theorem exterior_power_skew_adjoint_sign (R : realFieldType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (f a : {linear V -> V}) (ha : is_adjoint B B f a)
    (hf : is_skewsymmetric_endomorphism B f) m (x : exterior_power V m) :
  exterior_power_map a m x = (-1 : R)^+m *: exterior_power_map f m x.
Proof.
apply: exterior_power_map_scale => v.
rewrite scaleN1r; exact: (proj1 (skewsymmetric_iff_adjoint_negative hB ha) hf).
Qed.

(** Source for [exterior_power_orthogonal]: Federer 1.7.6,
    p. 33, an exterior power of an orthogonal injection is orthogonal. *)
Theorem exterior_power_orthogonal (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) : is_orthogonal_map B C f -> forall m,
  is_orthogonal_map (@exterior_inner_form R h2 V B hB m)
    (@exterior_inner_form R h2 U C hC m) (exterior_power_map f m).
Proof. move=> hf m x y; exact (@exterior_inner_orthogonal_natural R h2 V U B C hB hC f hf m x y). Qed.

(** Source for [exterior_power_orthogonal_projection]: Federer
    1.7.6, p. 33, an exterior power of an orthogonal projection
    is an orthogonal projection, including degree zero. *)
Theorem exterior_power_orthogonal_projection (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) : is_orthogonal_projection B C p -> forall m,
  is_orthogonal_projection (@exterior_inner_form R h2 V B hB m)
    (@exterior_inner_form R h2 U C hC m) (exterior_power_map p m).
Proof.
move=> [a [ho ha]] m; exists (exterior_power_map a m); split.
- exact (@exterior_power_orthogonal R h2 U V C B hC hB a ho m).
- exact (@exterior_power_adjoint R h2 U V C B hC hB a p ha m).
Qed.
