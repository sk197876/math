(** Federer (1969), 1.7.3, p. 29: assembling an orthogonal invariant
    decomposition after splitting off a minimal piece. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient InnerProductUP OrthogonalComplement
  MinimalInvariantUP OrthogonalDecompositionUP InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_decomposition_snoc]: Federer 1.7.3,
    p. 29, supporting assembly step: append a minimal invariant
    piece Z to a decomposition of an orthogonal complementary piece Q. *)
Theorem orthogonal_decomposition_snoc (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> V})
    (W Q Z : subspace V)
    (hQW : forall x, Q x -> W x) (hZW : forall x, Z x -> W x)
    (hQZ : forall x, Q x -> orthogonal_complement hB Z x)
    (hZ : is_minimal_invariant_subspace f Z)
    (hs : forall x, W x -> exists z q, Z z /\ Q q /\ x = z+q)
    s (A : 'I_s -> subspace V)
    (hA : is_orthogonal_invariant_decomposition_of B f Q A) :
  is_orthogonal_invariant_decomposition_of B f W (ordinal_snoc A Z).
Proof.
constructor.
- move=> i; case: (unliftP ord_max i) => [j ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last => x hx.
  + apply: hQW; exact: (@decomposition_of_contained R V B f Q s A hA j x hx).
  + exact: hZW hx.
- move=> i; case: (unliftP ord_max i) => [j ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact (@decomposition_of_minimal R V B f Q s A hA j).
  + exact hZ.
- move=> i j; case: (unliftP ord_max i) => [a ->|->];
    case: (unliftP ord_max j) => [b ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last => hij x y hx hy.
  + apply: (@decomposition_of_orthogonal R V B f Q s A hA a b _ x y hx hy).
    by move: hij; rewrite (inj_eq (@lift_inj s.+1 (ord_max : 'I_s.+1))).
  + have hqx := @decomposition_of_contained R V B f Q s A hA a x hx.
    exact (@hQZ x hqx y hy).
  + have hqy := @decomposition_of_contained R V B f Q s A hA b y hy.
    rewrite (inner_symmetric hB); exact (@hQZ y hqy x hx).
  + by move: hij; rewrite eqxx.
- move=> x hx; have [z [q [hz [hq he]]]] := hs x hx.
  have [a [ha hqa]] := @decomposition_of_spans R V B f Q s A hA q hq.
  exists (ordinal_snoc a z); split.
  + move=> i; case: (unliftP ord_max i) => [j ->|->];
      rewrite ?ordinal_snoc_lift ?ordinal_snoc_last; [exact: ha | exact hz].
  + rewrite big_ord_recr ordinal_snoc_last he hqa addrC.
    congr (_ + _); apply: eq_bigr => i _; by rewrite ordinal_snoc_before.
Qed.
