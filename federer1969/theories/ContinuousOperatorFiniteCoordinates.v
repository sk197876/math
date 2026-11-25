(** Federer (1969), 3.1.1, p. 211: when the source is finite
    dimensional, finitely many basis evaluations control the
    operator norm. This supports completeness and separability of
    the operator space used in the Borel differential argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra ring.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension Annihilator
  NormDifferentialUP NormFiniteLinearBound NormOperatorNormUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_operator_finite_coordinate_bound]:
    finite-dimensional source coordinates control the norm on Z
    in Federer 3.1.1, p. 211. The bound is uniform over operators;
    no finite-dimensional hypothesis is imposed on their target. *)
Theorem continuous_operator_finite_coordinate_bound (R : realType)
    (X Y Z : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    n (e : 'I_n -> X) (he : is_basis e) :
  exists K : R, 0 < K /\ forall z r, 0 <= r ->
    (forall i, NY (evaluation z (e i)) <= r) -> ZN z <= K*r.
Proof.
have hc i : exists C : R, 0 <= C /\ forall x, `|dual_basis he i x| <= C*NX x.
  exact: (@norm_finite_linear_bounded R X R^o NX (fun t => `|t|)
    hNX (@scalar_absolute_value_norm R) n e he (dual_basis he i)).
pose c i := sval (constructive_indefinite_description (hc i)).
have hci i := svalP (constructive_indefinite_description (hc i)).
pose S := \sum_(i<n) c i.
have hS : 0 <= S by apply: sumr_ge0=> i _; exact: (hci i).1.
exists (S+1); split; first by lra.
move=> z r hr hz; apply: (norm_operator_least (continuous_operator_norm_laws hZ z)).
- apply: mulr_ge0=> //; by lra.
- move=> x.
  have hex : evaluation z x=\sum_(i<n) dual_basis he i x *: evaluation z (e i).
    by rewrite {1}(@basis_vector_expansion R X n e he x) linear_sum;
      apply: eq_bigr=> i _; rewrite linearZ.
  rewrite hex; apply: le_trans (real_seminorm_sum hNY.1 _) _.
  have hs : (\sum_(i<n) NY (dual_basis he i x *: evaluation z (e i)))
      <= \sum_(i<n) (c i*NX x)*r.
    apply: ler_sum=> i _; rewrite (real_seminorm_scale hNY.1).
    apply: ler_pM.
    + exact: normr_ge0.
    + exact: real_seminorm_nonnegative hNY.1 _.
    + exact: (hci i).2.
    + exact: hz.
  rewrite -!mulr_suml in hs.
  apply: le_trans hs _.
  have hn := real_seminorm_nonnegative hNX.1 x.
  change ((S*NX x)*r <= ((S+1)*r)*NX x); nra.
Qed.
