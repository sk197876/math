(** Federer (1969), 1.7.3, p. 29: existence of a finite orthogonal
    decomposition into minimal invariant subspaces. Private existence proof,
    imported only by its seal and audit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  InnerProductUP OrthogonalComplement SymmetricEndomorphisms
  MinimalInvariantUP MinimalInvariantExistence OrthogonalDecompositionUP
  OrthogonalDecompositionExtension InvariantOrthogonalSplit
  AnnihilatorDimension SubspaceDimensionOrder FiniteSpans FiniteSpanSpace
  Annihilator FiniteDualDimension Hom InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable f : {linear V -> V}.
Hypothesis hf : is_symmetric_endomorphism B f \/ is_skewsymmetric_endomorphism B f.

(** Source for [orthogonal_relative_decomposition_witness]:
    Federer 1.7.3, p. 29, supporting relative decomposition,
    proved by induction on the dimension of the invariant subspace. *)
Theorem orthogonal_relative_decomposition_witness k (W : subspace V)
    (a : 'I_k -> subspace_space W) : is_basis a -> invariant_subspace f W ->
  exists s (A : 'I_s -> subspace V),
    is_orthogonal_invariant_decomposition_of B f W A.
Proof.
move: k W a; elim/ltn_ind => k IH W a ha hW.
have [hne|hzero] := pselect (exists x, W x /\ x != 0); last first.
  exists 0%N, (fun _ : 'I_0 => W); constructor.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> x hx; exists (fun _ : 'I_0 => (0 : V)); split.
    + move=> i; by have := ltn_ord i; rewrite ltn0.
    + rewrite big_ord0; have [->|hn] := eqVneq x 0; first by [].
      exfalso; apply: hzero; by exists x.
have [Z [hZW hZ]] := @minimal_invariant_subspace_exists R V n b hb f W hW hne.
have [l [c [hc hl]]] := @finite_subspace_basis_exists R V n b hb Z.
pose Q := @relative_orthogonal_complement R V B hB W Z.
have hQW : forall x, Q x -> W x by move=> x [hx _].
have hQZ : forall x, Q x -> orthogonal_complement hB Z x by move=> x [_ hx].
have hQ : invariant_subspace f Q.
  exact (@relative_orthogonal_complement_invariant R V B hB f hf W Z hW
    (minimal_invariant_stable hZ)).
have [m [d [hd hm]]] := @finite_subspace_basis_exists R V n b hb Q.
have hmk : (m < k)%N.
  apply: (@proper_subspace_dimension_lt R V Q W hQW m d hd k a ha).
  have [x [hx hn]] := minimal_invariant_nonzero hZ.
  exists x; split; first exact: hZW hx.
  move=> hqx.
  have hz := @orthogonal_complement_intersection_zero R V B hB Z x hx (hQZ x hqx).
  by move: hn; rewrite hz eqxx.
have [s [A hA]] := IH m hmk Q d hd hQ.
exists s.+1, (ordinal_snoc A Z).
apply: (@orthogonal_decomposition_snoc R V B hB f W Q Z hQW hZW hQZ hZ _ s A hA).
move=> x hx; exact (@relative_orthogonal_split R V B hB W Z hZW l c hc x hx).
Qed.

(** Source for [orthogonal_decomposition_witness]: Federer
    1.7.3, p. 29, every symmetric or skewsymmetric map in finite
    dimension admits finitely many mutually orthogonal minimal
    nonzero invariant summands spanning the entire space. *)
Theorem orthogonal_decomposition_witness :
  exists s (A : 'I_s -> subspace V),
    is_orthogonal_invariant_decomposition B f A.
Proof.
pose W := finite_span_subspace b.
have hW x : W x by exists (fun i => dual_basis hb i x); exact: basis_vector_expansion.
have hWi : invariant_subspace f W by move=> x hx; exact: hW.
have [k [a [ha hk]]] := @finite_subspace_basis_exists R V n b hb W.
have [s [A hA]] := @orthogonal_relative_decomposition_witness k W a ha hWi.
exists s, A; constructor.
- exact: decomposition_of_minimal hA.
- exact: decomposition_of_orthogonal hA.
- move=> x; exact: (@decomposition_of_spans R V B f W s A hA x (hW x)).
Qed.
End Construction.
