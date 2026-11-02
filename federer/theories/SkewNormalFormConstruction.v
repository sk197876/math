(** Federer (1969), 1.7.3, pp. 29-30: assemble the normal form through
    orthogonal invariant pieces of dimension at most two. Private existence
    construction, used only by its seal and the assumption audit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  InnerProductUP Bilinear OrthogonalComplement SymmetricEndomorphisms
  MinimalInvariantUP MinimalInvariantExistence MinimalSkewBlocks
  InvariantOrthogonalSplit AnnihilatorDimension SubspaceDimensionOrder
  SkewNormalFormUP SkewNormalFormExtension FiniteSpans FiniteSpanSpace
  Annihilator FiniteDualDimension Hom InfiniteSequence OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable f : {linear V -> V}.
Hypothesis hf : is_skewsymmetric_endomorphism B f.

(** Source for [skew_relative_normal_witness]: Federer
    1.7.3, pp. 29-30, supporting relative normal form proved
    by splitting off one minimal invariant piece at each step. *)
Theorem skew_relative_normal_witness k (W : subspace V)
    (e : 'I_k -> subspace_space W) : is_basis e -> invariant_subspace f W ->
  exists m (a b : 'I_m -> V) (lambda : 'I_m -> R),
    is_skew_normal_form_on B f W a b lambda.
Proof.
move: k W e; elim/ltn_ind => k IH W e he hW.
have [hne|hzero] := pselect (exists x, W x /\ x != 0); last first.
  exists 0%N, (fun _ : 'I_0 => (0 : V)), (fun _ : 'I_0 => (0 : V)),
    (fun _ : 'I_0 => (0 : R)); constructor.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> [i bi]; by have := ltn_ord i; rewrite ltn0.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
  - move=> x hx y; rewrite big_ord0.
    have [->|hn] := eqVneq x 0; first by rewrite linear0 (bil0l (inner_bilinear hB)).
    exfalso; apply: hzero; by exists x.
have [Z [hZW hZ]] := @minimal_invariant_subspace_exists R V n b hb f W hW hne.
have [l [c [hc hl]]] := @finite_subspace_basis_exists R V n b hb Z.
pose Q := @relative_orthogonal_complement R V B hB W Z.
have hQW : forall x, Q x -> W x by move=> x [hx _].
have hQZ : forall x, Q x -> orthogonal_complement hB Z x by move=> x [_ hx].
have hQ : invariant_subspace f Q.
  exact (@relative_orthogonal_complement_invariant R V B hB f (or_intror hf)
    W Z hW (minimal_invariant_stable hZ)).
have [j [d [hd hj]]] := @finite_subspace_basis_exists R V n b hb Q.
have hjk : (j < k)%N.
  apply: (@proper_subspace_dimension_lt R V Q W hQW j d hd k e he).
  have [x [hx hn]] := minimal_invariant_nonzero hZ.
  exists x; split; first exact: hZW hx.
  move=> hqx.
  have hz := @orthogonal_complement_intersection_zero R V B hB Z x hx (hQZ x hqx).
  by move: hn; rewrite hz eqxx.
have hs x : W x -> exists z q, Z z /\ Q q /\ x = z+q.
  exact (@relative_orthogonal_split R V B hB W Z hZW l c hc x).
have [m [a [a' [lambda hN]]]] := IH j hjk Q d hd hQ.
have [hz|[u [v [r [hu [hv [hp hspan]]]]]]] :=
  @minimal_skew_block_alternative R V B hB n b hb f hf Z hZ.
- exists m, a, a', lambda.
  exact (@skew_normal_extend_zero R V B hB f W Q Z hQW hQZ hs m a a' lambda hN hz).
- exists m.+1, (ordinal_snoc a u), (ordinal_snoc a' v), (ordinal_snoc lambda r).
  exact (@skew_normal_extend_pair R V B hB f W Q Z hQW hZW hQZ hs
    m a a' lambda hN u v r hu hv hp hspan).
Qed.

(** Source for [skew_normal_witness]: Federer 1.7.3,
    pp. 29-30, the skewsymmetric map's bilinear form is a
    finite sum of nonnegative orthonormal two-dimensional blocks. *)
Theorem skew_normal_witness :
  exists m (a c : 'I_m -> V) (lambda : 'I_m -> R),
    orthonormal_family B (paired_family a c) /\
    (forall i, 0 <= lambda i) /\
    forall x y, B (f x) y = \sum_i lambda i * skew_pair_form B (a i) (c i) x y.
Proof.
pose W := finite_span_subspace b.
have hW x : W x by exists (fun i => dual_basis hb i x); exact: basis_vector_expansion.
have hWi : invariant_subspace f W by move=> x hx; exact: hW.
have [k [e [he hk]]] := @finite_subspace_basis_exists R V n b hb W.
have [m [a [c [lambda hN]]]] := @skew_relative_normal_witness k W e he hWi.
exists m, a, c, lambda; split; first exact: skew_normal_orthonormal hN.
split; first exact: skew_normal_nonnegative hN.
move=> x y; exact (@skew_normal_equation R V B f W m a c lambda hN x (hW x) y).
Qed.
End Construction.
