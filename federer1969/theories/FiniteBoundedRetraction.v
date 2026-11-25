(** Federer (1969), 1.10.5, p. 48: supporting finite-dimensional reduction
    in the positivity proof for mass. The construction extends the finite
    coordinate functionals with Hahn-Banach to obtain a bounded linear
    retraction r onto U. For the inclusion j : U -> V, the identity is
    r (j u) = u for every u in U. Neither completeness nor a
    finite-dimensional ambient space is required. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Hom LinearBasis FiniteDualDimension Annihilator
  RealNormUP RealSeminormOperations InnerProductUP InnerNorm InnerNormInequalities
  OrthonormalFamilies OrthonormalParseval FiniteBasisInnerWitness FiniteNormLowerBound
  BoundedFunctionalExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_bounded_linear_retraction]: Federer 1.10.5, p. 48,
    supporting positivity argument. Every finite-dimensional linear subspace
    of a normed space has a linear retraction with a finite norm bound.
    Neither completeness nor a finite-dimensional ambient space is required. *)
Theorem finite_bounded_linear_retraction (R : realType) (U V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> U) (he : is_basis e)
    (j : {linear U -> V}) (hj : injective j) :
  exists r : {linear V -> U}, (forall u, r (j u)=u) /\
    exists D : R, 0 <= D /\ forall v, N (j (r v)) <= D * N v.
Proof.
have [B [hB ho]] := finite_basis_inner_product_witness he.
have hNU := real_norm_injective_precompose hN hj.
have [C [hC hc]] := @finite_norm_inner_lower_bound R U B hB
  (fun u => N (j u)) hNU n e he.
have hcoord i u : `|dual_basis he i u| <= C * N (j u).
  rewrite (@orthonormal_basis_inner_coordinate R U B hB _ e ho he).
  have hi : inner_norm hB (e i) = 1.
    apply: inner_norm_value; first exact: ler01.
    by rewrite expr1n ho eqxx.
  have hh := inner_cauchy hB u (e i); rewrite hi mulr1 in hh.
  exact: le_trans hh (hc u).
have hg i : exists g : {linear V -> R^o},
    (forall u, g (j u)=dual_basis he i u) /\ forall v, `|g v| <= C * N v.
  exact (@bounded_functional_extension R U V N (proj1 hN) j hj
    (GRing.Linear.clone _ _ _ _ (dual_basis he i) _) C (ltW hC) (hcoord i)).
pose g := fun i => projT1 (cid (hg i)).
have gP i := projT2 (cid (hg i)).
pose r := fun v => \sum_i g i v *: e i.
have hr : linear r.
  move=> a v w; rewrite /r scaler_sumr -big_split; apply: eq_bigr=> i _.
  by rewrite linearP scalerDl scalerA.
exists (hom_as_linear (@HomMap R V U r (introT (asboolP _) hr))); split.
- move=> u; change (r (j u)=u); rewrite /r.
  under eq_bigr do rewrite (proj1 (gP _) u).
  exact: esym (@basis_vector_expansion R U n e he u).
- exists (C * \sum_i N (j (e i))); split.
  + apply: mulr_ge0 (ltW hC) _; apply: sumr_ge0=> i _.
    exact: real_seminorm_nonnegative (proj1 hN) (j (e i)).
  + move=> v; change (N (j (r v)) <= (C * \sum_i N (j (e i))) * N v).
    rewrite /r linear_sum.
    apply: le_trans (@real_seminorm_sum R V N (proj1 hN) (Finite.clone 'I_n _)
      (fun i => j (g i v *: e i))) _.
    rewrite mulrAC !mulr_sumr; apply: ler_sum=> i _.
    rewrite linearZ (real_seminorm_scale (proj1 hN)).
    exact (ler_wpM2r (real_seminorm_nonnegative (proj1 hN) (j (e i)))
      (proj2 (gP i) v)).
Qed.
