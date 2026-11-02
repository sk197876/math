(** Private gluing witness for Federer (1969), 2.6.6, pp. 120–121:
    consistent factor integrals define a single functional on the union of
    inverse-limit pullbacks. Equality of presentations has been proved using
    the limit norm bound. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseDaniellPullbackEquality InverseLimitPullbackLattice CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_daniell_gluing_exists]: construction of
    the functional on the directed pullback union, repeating the
    gluing step for the inverse limits in Federer 2.6.6,
    pp. 120–121. Values outside the union are immaterial. *)
Theorem inverse_daniell_gluing_exists (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) (u0 : prod_topology Y) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_consistent_inverse_daniell_family le b A ->
  exists G : (X -> R) -> R, forall i f, compactly_supported_continuous_functions f -> G (f \o p i)=A i f.
Proof.
move=> hs hl hA.
have hv : forall g, inverse_limit_pullbacks p g -> exists r : R,
    forall i (f : Y i -> R), compactly_supported_continuous_functions f -> g=f \o p i -> r=A i f.
  move=> g [j [t [ht ->]]]; exists (A j t)=> i f hf he.
  exact: (@inverse_daniell_pullback_equal R I le Y b X p A u0 hs hl hA j i t f ht hf he).
pose G := fun g : X -> R=> if pselect (inverse_limit_pullbacks p g) is left hg
  then sval (cid (hv g hg)) else 0.
exists G=> i f hf; rewrite /G; case: pselect=> [hg|hn].
- exact: (svalP (cid (hv _ hg))) i f hf (erefl _).
- exfalso; apply: hn; by exists i,f.
Qed.
