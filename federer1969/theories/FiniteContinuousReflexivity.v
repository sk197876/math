(** Federer (1969), 2.4.12, p. 88, final parenthesis: every
    finite-dimensional normed space is reflexive. The supporting algebraic
    representation extends functionals from a subspace of the algebraic dual
    and applies the finite dual basis. Source context and independently
    verified algebraic references: FiniteAlgebraicBidual.v. No completeness
    assumption is needed for this finite-dimensional claim. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP LinearBasis LinearRetraction FiniteAlgebraicBidual
  RealNormUP ContinuousDualUP ContinuousDualNorm ContinuousBidualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [finite_dual_subspace_representative]: supporting
    algebraic step for reflexivity in Federer 2.4.12, p. 88.
    Any functional on an injectively represented subspace of a finite
    algebraic dual is evaluation at a vector. The stronger arbitrary-field
    statement does not assume that this subspace is the entire dual. *)
Lemma finite_dual_subspace_representative (K : fieldType) (I : finType)
    (V D : lmodType K) (e : I -> V) (he : is_basis e)
    (ed : Hom D (Hom V K^o)) (hi : injective ed) (ell : Hom D K^o) :
  exists y : V, forall d : D, ell d = ed d y.
Proof.
pose r := linear_retraction (i:=hom_as_linear ed) hi.
pose ell' := hom_of_linear (linear_comp (hom_as_linear ell) r).
have [y hy] := finite_algebraic_bidual_representative he ell'.
exists y=> d; have hh := hy (ed d).
change (ell (r (ed d)) = ed d y) in hh.
by rewrite /r linear_retractionK in hh.
Qed.

(** Source for [finite_continuous_dual_reflexive]: direct
    finite-dimensional reflexivity in Federer 2.4.12, p. 88.
    The abstract dual and bidual may be any implementations satisfying
    their specifications; the supplied canonical embedding is surjective. *)
Theorem finite_continuous_dual_reflexive (R : realType) (I : finType)
    (V D B : lmodType R) (e : I -> V) (he : is_basis e)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom V B) : is_bidual_embedding ed eb tau ->
  is_reflexive_embedding tau.
Proof.
move=> ht b.
have [y hy] := finite_dual_subspace_representative he
  (continuous_dual_injective hD) (eb b).
exists y; apply: (continuous_dual_injective hB); apply: hom_ext=> a.
by rewrite ht -hy.
Qed.
