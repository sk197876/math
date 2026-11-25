(** Federer (1969), 1.7.6, p. 33: determinant of an adjoint and squared
    determinant of an orthogonal endomorphism. These proofs use the
    intrinsic action on the top exterior power, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerExterior
  InnerExteriorPositivity InnerExteriorNaturality ExteriorAdjoint
  AdjointUP OrthogonalMaps ExteriorDeterminant ExteriorGrading
  ExteriorMaps LinearBasis Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Determinant.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation E := (@exterior_inner_form R h2 V B hB n).
Local Notation hE := (@exterior_inner_productP R h2 V B hB n).
Local Notation t := (@top_vector R n V b).

(** Source for [adjoint_determinant]: Federer 1.7.6, p. 33,
    det(adjoint f) = det(f), obtained by evaluating the exterior adjoint
    identity on a nonzero top-degree vector. *)
Theorem adjoint_determinant (f a : {linear V -> V})
    (ha : is_adjoint B B f a) : det h2 hb a = det h2 hb f.
Proof.
have ht : E t t != 0 by rewrite (inner_self_eq0 hE); exact: top_vector_nonzero.
have hh := @exterior_power_adjoint R h2 V V B B hB hB f a ha n t t.
rewrite !(@detE R h2 n V b hb) (bilZr (inner_bilinear hE)) (bilZl (inner_bilinear hE)) in hh.
apply: (mulIf ht); exact hh.
Qed.

(** Source for [orthogonal_determinant_square]: Federer 1.7.6,
    p. 33, det(f)^2 = 1 for an orthogonal endomorphism. The
    top exterior map preserves the squared length of its generator. *)
Theorem orthogonal_determinant_square (f : {linear V -> V})
    (hf : is_orthogonal_map B B f) : (det h2 hb f)^+2 = 1.
Proof.
have ht : E t t != 0 by rewrite (inner_self_eq0 hE); exact: top_vector_nonzero.
have hh := @exterior_inner_orthogonal_natural R h2 V V B B hB hB f hf n t t.
rewrite !(@detE R h2 n V b hb) (inner_scale_square hE) in hh.
apply: (mulIf ht); by rewrite mul1r.
Qed.
End Determinant.
