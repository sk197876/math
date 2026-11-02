(** Federer (1969), 1.10.5, p. 48: positive definiteness of mass,
    finite-dimensional step. We use an auxiliary inner product and the
    already proved product estimate on p. 47. The given arbitrary norm
    remains the norm defining the mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import LinearBasis InnerProductUP InnerNorm
  RealNormUP SymmetricAlgebra SymmetricGrading SymmetricFormIsomorphism
  SymmetricDecompositionCosts SymmetricProjectiveMass SymmetricProjectiveSeminorm
  SymmetricProjectiveMaximality SymmetricInnerNorm SymmetricInnerProductBound
  FiniteBasisInnerWitness FiniteNormLowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_inner_mass_comparison]: Federer 1.10.5,
    pp. 47-48, supporting comparison between the induced inner norm
    and mass. If |v| is at most C N(v), then the inner norm
    of an m-vector is at most sqrt(m!) C^m times its mass. *)
Theorem symmetric_inner_mass_comparison (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_seminorm N) C (hC : 0 <= C)
    (hb : forall v, inner_norm hB v <= C * N v)
    m (hm : (0<m)%N) (x : symmetric_power V m) :
  symmetric_inner_norm hB x <=
    (Num.sqrt ((m`!)%:R : R) * C^+m) * symmetric_projective_mass hN hm x.
Proof.
apply: (@symmetric_projective_mass_maximal R V N hN m hm _
  (proj1 (symmetric_inner_normP hB m)) _
  (mulr_ge0 (sqrtr_ge0 _) (exprn_ge0 _ hC)) _ x).
move=> t; apply: le_trans (symmetric_inner_tuple_norm_bound hB t) _.
rewrite -mulrA; apply: (ler_wpM2l (sqrtr_ge0 ((m`!)%:R : R))).
rewrite /symmetric_tuple_cost.
have he : C^+m * \prod_(i<m) N (tnth t i) =
    \prod_(i<m) (C * N (tnth t i)).
  by rewrite big_split prodr_const card_ord.
rewrite he; apply: ler_prod=> i _; apply/andP; split.
- exact: inner_norm_nonnegative.
- exact: hb.
Qed.

(** Source for [finite_symmetric_projective_mass_norm]: Federer
    1.10.5, p. 48, mass is a norm, here for a finite-dimensional
    space. The arbitrary-dimensional reduction follows separately.
    The zero-dimensional case is included by the norm-comparison lemma. *)
Theorem finite_symmetric_projective_mass_norm (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (he : is_basis e)
    m (hm : (0<m)%N) : is_real_norm (symmetric_projective_mass (proj1 hN) hm).
Proof.
split; first exact: symmetric_projective_mass_seminorm.
move=> x hx.
have [B [hB _]] := finite_basis_inner_product_witness he.
have [C [hC hc]] := @finite_norm_inner_lower_bound R V B hB N hN n e he.
have hb := @symmetric_inner_mass_comparison R V B hB N (proj1 hN) C (ltW hC) hc m hm x.
rewrite hx mulr0 in hb.
have hz : symmetric_inner_norm hB x=0.
  apply/eqP; rewrite eq_le hb (symmetric_inner_norm_nonnegative hB x).
  by [].
move/eqP: hz; by rewrite symmetric_inner_norm_eq0=> /eqP.
Qed.
