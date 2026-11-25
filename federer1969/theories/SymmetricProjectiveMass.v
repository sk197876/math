(** Federer (1969), 1.10.5, p. 48, the finite-decomposition infimum. This
    public interface names the infimum seminorm; identification with
    Federer's dual supremum is proved separately. Only the sealed infimum
    laws are used here. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricFormIsomorphism SymmetricDecompositions SymmetricDecompositionCosts
  SymmetricMassInfimumUP SymmetricMassInfimumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Interface.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable m : nat.
Variable hm : (0<m)%N.

(** Source for [symmetric_projective_mass]: Federer 1.10.5,
    p. 48, the infimum over all finite decompositions of a
    positive-degree symmetric vector, exposed through its sealed specification. *)
Definition symmetric_projective_mass (x : symmetric_power V m) : R :=
  @SymmetricMassInfimum.value R V N hN m hm x.

(** Source for [symmetric_projective_massP]: Federer 1.10.5,
    p. 48, the public value satisfies the nonnegative infimum laws. *)
Lemma symmetric_projective_massP x :
  is_symmetric_mass_infimum N x (symmetric_projective_mass x).
Proof. exact: SymmetricMassInfimum.laws. Qed.

(** Source for [symmetric_projective_mass_nonnegative]: Federer
    1.10.5, p. 48, the infimum of decomposition costs is nonnegative. *)
Lemma symmetric_projective_mass_nonnegative x : 0 <= symmetric_projective_mass x.
Proof. exact: symmetric_mass_infimum_nonnegative (symmetric_projective_massP x). Qed.

(** Source for [symmetric_projective_mass_cost_bound]: Federer
    1.10.5, p. 48, every finite decomposition bounds its mass infimum. *)
Lemma symmetric_projective_mass_cost_bound x s :
  symmetric_decomposition x s -> symmetric_projective_mass x <= symmetric_decomposition_cost N s.
Proof. exact (@symmetric_mass_infimum_lower R V N m x _ (symmetric_projective_massP x) s). Qed.

(** Source for [symmetric_projective_mass_approximate]: Federer
    1.10.5, p. 48, costs can approach the infimum within
    every positive error; attainment is not assumed in arbitrary dimension. *)
Lemma symmetric_projective_mass_approximate x eps : 0 < eps -> exists s,
  symmetric_decomposition x s /\ symmetric_decomposition_cost N s < symmetric_projective_mass x+eps.
Proof. exact (@symmetric_mass_infimum_approximate R V N m x _ (symmetric_projective_massP x) eps). Qed.

(** Source for [symmetric_projective_mass_greatest]: Federer
    1.10.5, p. 48, every lower bound for the decomposition costs
    is below the public infimum. *)
Lemma symmetric_projective_mass_greatest x c :
  (forall s, symmetric_decomposition x s -> c <= symmetric_decomposition_cost N s) ->
  c <= symmetric_projective_mass x.
Proof. exact (@symmetric_mass_infimum_greatest R V N m x _ (symmetric_projective_massP x) c). Qed.

(** Source for [symmetric_projective_mass_zero]: Federer 1.10.5,
    p. 48, the zero vector has zero mass infimum because the
    empty decomposition has cost zero. *)
Lemma symmetric_projective_mass_zero : symmetric_projective_mass 0 = 0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last exact: symmetric_projective_mass_nonnegative.
have hh := symmetric_projective_mass_cost_bound (symmetric_decomposition_zero V m).
by rewrite /symmetric_decomposition_cost big_nil in hh.
Qed.

(** Source for [symmetric_projective_mass_tuple_bound]: Federer 1.10.5, p.
    48, a single product has mass infimum at most the product of its factor
    lengths *)
Lemma symmetric_projective_mass_tuple_bound (t : m.-tuple V) :
  symmetric_projective_mass (symmetric_tuple_component t) <= symmetric_tuple_cost N t.
Proof.
have hd : symmetric_decomposition (symmetric_tuple_component t) [::t].
  by rewrite /symmetric_decomposition big_cons big_nil addr0.
have hh := symmetric_projective_mass_cost_bound hd.
by rewrite /symmetric_decomposition_cost big_cons big_nil addr0 in hh.
Qed.
End Interface.
