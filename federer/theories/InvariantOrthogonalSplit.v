(** Federer (1969), 1.7.3, p. 29: splitting an invariant subspace into a
    minimal invariant piece and its relative orthogonal complement. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  InnerProductUP OrthogonalComplement OrthogonalSubspaceSplit
  SymmetricEndomorphisms AnnihilatorIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RelativeSplit.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear V -> V}.
Hypothesis hf : is_symmetric_endomorphism B f \/ is_skewsymmetric_endomorphism B f.
Variable W Z : subspace V.
Hypothesis hZW : forall x, Z x -> W x.
Hypothesis hW : invariant_subspace f W.
Hypothesis hZ : invariant_subspace f Z.

(** Source for [relative_orthogonal_complement]: Federer
    1.7.3, p. 29, supporting definition of the orthogonal
    complement of Z inside W as W intersected with Z perpendicular. *)
Definition relative_orthogonal_complement :=
  subspace_intersection W (orthogonal_complement hB Z).

(** Source for [relative_orthogonal_complement_invariant]:
    Federer 1.7.3, p. 29, both pieces of the relative orthogonal
    splitting remain invariant for symmetric or skewsymmetric maps. *)
Lemma relative_orthogonal_complement_invariant :
  invariant_subspace f relative_orthogonal_complement.
Proof.
move=> x [hx ho]; split; first exact: hW hx.
case: hf => hfs.
- exact: (@symmetric_orthogonal_reducibility R V B hB f Z hfs hZ x ho).
- exact: (@skewsymmetric_orthogonal_reducibility R V B hB f Z hfs hZ x ho).
Qed.

(** Source for [relative_orthogonal_split]: Federer 1.7.3,
    p. 29, every vector of W is the sum of a vector of Z and
    a vector in W intersected with the perpendicular of Z. *)
Theorem relative_orthogonal_split k (a : 'I_k -> subspace_space Z)
    (ha : is_basis a) x : W x ->
  exists z q, Z z /\ relative_orthogonal_complement q /\ x = z+q.
Proof.
move=> hx; have [z [q [hz [hq he]]]] :=
  @finite_subspace_orthogonal_split R V B hB Z k a ha x.
exists z, q; split; first exact hz.
split; last exact he.
split; last exact hq.
have hqE : q = x-z by rewrite he addrAC subrr add0r.
rewrite hqE; exact: subspace_sub hx (hZW hz).
Qed.
End RelativeSplit.
