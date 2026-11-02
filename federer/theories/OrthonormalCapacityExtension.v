(** Federer (1969), 1.7.3, p. 30: extending the normalised nonzero images
    across the kernel in the orthogonal-injection factorisation. A
    prescribed independent n-family expresses dimension at least n; the
    ambient target may be infinite-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerNormalization InnerNorm
  OrthonormalFamilies OrthonormalProjection FiniteIndependence FiniteSpans
  FiniteBasisCriterion FiniteBasisComparison FiniteDimension InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Capacity.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable u : 'I_n -> V.
Hypothesis hu : finite_independent u.

(** Source for [orthonormal_capacity_missing_vector]: Federer
    1.7.3, p. 30, supporting dimension argument: fewer than n
    orthonormal vectors cannot span a space with n independent vectors. *)
Lemma orthonormal_capacity_missing_vector k (e : 'I_k -> V)
    (he : orthonormal_family B e) : (k < n)%N ->
  exists x, ~ in_finite_span e x.
Proof.
move=> hkn; apply: contrapT => hnone.
have hs x : in_finite_span e x.
  apply: contrapT => hx; apply: hnone; by exists x.
have hi := @orthonormal_independent R V B hB (Finite.clone 'I_k _) e he.
have hb := finite_basis_criterion hi hs.
have hd := @finite_independent_dimension R (finite_basis_vect hb) n u hu.
rewrite finite_basis_dimension card_ord in hd.
by have := leq_ltn_trans hd hkn; rewrite ltnn.
Qed.

(** Source for [orthonormal_capacity_next_vector]: Federer
    1.7.3, p. 30, choose a unit vector perpendicular to a
    shorter orthonormal family, without a finite-dimensional target. *)
Lemma orthonormal_capacity_next_vector k (e : 'I_k -> V)
    (he : orthonormal_family B e) : (k < n)%N ->
  exists v, B v v = 1 /\ forall i, B v (e i) = 0.
Proof.
move=> hk; have [x hx] := orthonormal_capacity_missing_vector he hk.
have hn := @orthonormal_residual_nonzero R V B hB k e x hx.
exists (inner_normalize hB (x - orthonormal_projection hB e x)); split.
- exact: inner_normalize_square hn.
- move=> i; apply: inner_normalize_orthogonal.
  exact (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_k _) e he x i).
Qed.

(** Source for [orthonormal_capacity_extension]: Federer
    1.7.3, p. 30, extend an orthonormal family to length n
    preserving every prescribed vector, whenever the target has
    at least n independent vectors. *)
Theorem orthonormal_capacity_extension k (e : 'I_k -> V)
    (he : orthonormal_family B e) (hkn : (k <= n)%N) :
  exists d : 'I_n -> V, orthonormal_family B d /\
    forall i, d (widen_ord hkn i) = e i.
Proof.
pose P m := `[< exists (hkm : (k <= m)%N) (d : 'I_m -> V),
  (m <= n)%N /\ orthonormal_family B d /\
  forall i, d (widen_ord hkm i) = e i >].
have hp : exists m, P m.
  exists k; apply/asboolP; exists (leqnn k), e; split=> //; split=> // i.
  congr (e _); exact: val_inj.
have hub m : P m -> (m <= n)%N by move/asboolP=> [hkm [d [hm _]]].
have [m /asboolP [hkm [d [hm [hd hde]]]] hmax] := @ex_maxnP P n hp hub.
have hmn : m = n.
  apply/eqP; rewrite eqn_leq hm andTb; apply/negPn/negP => hn.
  have hlt : (m < n)%N by rewrite ltnNge.
  have [v [hv hve]] := orthonormal_capacity_next_vector hd hlt.
  pose hkm' := leq_trans hkm (leqnSn m).
  have hPm : P m.+1.
    apply/asboolP; exists hkm', (ordinal_snoc d v); split; first exact hlt.
    split; first exact: (@orthonormal_snoc R V B hB m d v hd hv hve).
    move=> i.
    have hi : widen_ord hkm' i = widen_ord (leqnSn m) (widen_ord hkm i).
      exact: val_inj.
    by rewrite hi ordinal_snoc_before hde.
  by have := hmax m.+1 hPm; rewrite ltnn.
subst m; exists d; split; first exact hd.
move=> i; have hi : widen_ord hkn i = widen_ord hkm i by apply: val_inj.
by rewrite hi hde.
Qed.
End Capacity.
