(** Consequences of the abstract finite-product laws supporting
    Federer (1969), 3.1.1(4), p. 210. All arguments below use only
    the specified linear coordinates and sum-norm equation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R : realType.
Variable m : nat.
Variable V : 'I_m -> lmodType R.
Variable N : forall i, V i -> R.
Arguments N i _ : clear implicits.
Hypothesis hN : forall i, is_real_norm (N i).
Arguments hN i : clear implicits.
Variable P : lmodType R.
Variable coordinate : forall i, Hom P (V i).
Arguments coordinate i : clear implicits.
Variable PN : P -> R.
Hypothesis hP : is_normed_family N coordinate PN.

(** Source for [normed_family_coordinate_bound]: each coordinate
    norm is bounded by the product sum norm, supporting the
    multilinear remainder estimate in 3.1.1(4), p. 210. *)
Lemma normed_family_coordinate_bound x i : N i (coordinate i x) <= PN x.
Proof.
rewrite (normed_family_norm hP) (bigD1 i) //= lerDl.
apply: sumr_ge0=> j _.
exact: real_seminorm_nonnegative (hN j).1 _.
Qed.

(** Source for [normed_family_is_norm]: the abstract product
    norm satisfies nonnegativity, homogeneity, the triangle inequality,
    and definiteness, supporting 3.1.1(4), p. 210. *)
Theorem normed_family_is_norm : is_real_norm PN.
Proof.
split.
- constructor.
  + move=> x; rewrite (normed_family_norm hP).
    apply: sumr_ge0=> i _; exact: real_seminorm_nonnegative (hN i).1 _.
  + move=> c x; rewrite !(normed_family_norm hP) mulr_sumr.
    apply: eq_bigr=> i _; rewrite linearZ /=.
    exact: (@real_seminorm_scale R (V i) (N i) (hN i).1 c (coordinate i x)).
  + move=> x y; rewrite !(normed_family_norm hP) -big_split /=.
    apply: ler_sum=> i _; rewrite linearD /=.
    exact: real_seminorm_triangle (hN i).1 _ _.
- move=> x hx; apply: (normed_family_extensional hP)=> i.
  rewrite linear0; apply: (hN i).2; apply/eqP; rewrite eq_le.
  apply/andP; split; last exact: real_seminorm_nonnegative (hN i).1 _.
  by have := normed_family_coordinate_bound x i; rewrite hx.
Qed.
End Laws.
