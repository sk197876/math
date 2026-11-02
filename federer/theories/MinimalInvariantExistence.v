(** Federer (1969), 1.7.3, p. 29: existence of minimal nonzero invariant
    subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  SymmetricEndomorphisms MinimalInvariantUP AnnihilatorDimension
  SubspaceDimensionOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [minimal_invariant_subspace_exists]: Federer
    1.7.3, p. 29, supporting existence of a minimal nonzero
    invariant subspace inside any nonzero invariant subspace in
    finite dimension. Symmetry is needed later for orthogonal splitting,
    but not for this minimum-dimension argument. *)
Theorem minimal_invariant_subspace_exists (R : fieldType) (V : lmodType R)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> V})
    (W : subspace V) (hW : invariant_subspace f W)
    (hne : exists x, W x /\ x != 0) :
  exists Z : subspace V, (forall x, Z x -> W x) /\ is_minimal_invariant_subspace f Z.
Proof.
pose P k := `[< exists (Z : subspace V) (a : 'I_k -> subspace_space Z),
  is_basis a /\ (forall x, Z x -> W x) /\ invariant_subspace f Z /\
  (exists x, Z x /\ x != 0) >].
have hP : exists k, P k.
  have [k [a [ha hk]]] := @finite_subspace_basis_exists R V n b hb W.
  exists k; apply/asboolP; exists W, a; repeat split=> //.
have [k /asboolP [Z [a [ha [hZW [hZ hneZ]]]]] hmin] := @ex_minnP P hP.
exists Z; split; first exact hZW.
constructor; [exact hneZ | exact hZ |].
move=> T hTZ hneT hT x hx.
have [htx|hntx] := pselect (T x); first exact htx.
have [l [c [hc hl]]] := @finite_subspace_basis_exists R V n b hb T.
have hlt := @proper_subspace_dimension_lt R V T Z hTZ l c hc k a ha
  (ex_intro _ x (conj hx hntx)).
have hPl : P l.
  apply/asboolP; exists T, c; split; first exact hc.
  split; first by move=> y hy; apply: hZW; exact: hTZ.
  by split.
have hle := hmin l hPl.
by have := leq_ltn_trans hle hlt; rewrite ltnn.
Qed.
