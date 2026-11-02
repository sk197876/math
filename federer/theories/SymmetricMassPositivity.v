(** Federer (1969), 1.10.5, p. 48: the mass is a norm on each positive
    symmetric power, in arbitrary dimension. We follow the finite-support
    and bounded-retraction argument. The ambient space is not assumed to
    possess a finite basis. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import LinearBasis FiniteSpanSpace SubspaceCarrier
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricPowerFunctor
  SymmetricFiniteReduction RealNormUP RealSeminormOperations
  SymmetricProjectiveMass SymmetricProjectiveSeminorm SymmetricMassMapBound
  SymmetricFiniteMassPositivity FiniteBoundedRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_projective_mass_norm]: Federer 1.10.5, p. 48, the
    positive-degree mass infimum defines a norm. A symmetric vector has
    finite support; a bounded retraction to that support transfers the
    finite-dimensional positivity result. *)
Theorem symmetric_projective_mass_norm (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (hm : (0<m)%N) :
  is_real_norm (symmetric_projective_mass (proj1 hN) hm).
Proof.
split; first exact: symmetric_projective_mass_seminorm.
move=> x hx.
have [n [e [he [_ [a ha]]]]] := symmetric_finite_dimensional_reduction x [::].
pose U := finite_span_vect he.
pose j := subspace_inclusion (finite_span_subspace e).
have hj : injective j := @subspace_val_injective R V (finite_span_subspace e).
have hNU := @real_norm_injective_precompose R U V N hN j hj.
have hb := finite_span_basisP he.
have [r [hr [D [hD hbound]]]] := @finite_bounded_linear_retraction R U V N hN
  n (finite_span_basis e) hb j hj.
have hM := @finite_symmetric_projective_mass_norm R U (fun u => N (j u)) hNU
  n (finite_span_basis e) hb m hm.
have hmap := @symmetric_projective_mass_map_bound R V U N (fun u => N (j u))
  (proj1 hN) (proj1 hNU) r D hD hbound m hm x.
rewrite hx mulr0 -ha (symmetric_power_mapK hr) in hmap.
have hz : symmetric_projective_mass (proj1 hNU) hm a=0.
  apply/eqP; rewrite eq_le hmap (real_seminorm_nonnegative (proj1 hM) a).
  by [].
have ha0 := proj2 hM a hz.
by rewrite -ha ha0 linear0.
Qed.

(** Source for [symmetric_projective_mass_positive]: Federer
    1.10.5, p. 48, positive definiteness in inequality form:
    a symmetric vector has positive mass exactly when it is nonzero. *)
Lemma symmetric_projective_mass_positive (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (hm : (0<m)%N)
    (x : symmetric_power V m) :
  (0 < symmetric_projective_mass (proj1 hN) hm x) = (x != 0).
Proof.
have hM := symmetric_projective_mass_norm hN hm.
exact (@real_norm_positive R (symmetric_power V m)
  (symmetric_projective_mass (proj1 hN) hm) (proj1 hM) (proj2 hM) x).
Qed.
