(** Private extension witness for Federer (1969), 2.6.6, pp. 120–121:
    normalized monotone consistent Daniell functionals extend to a compact
    Hausdorff inverse limit. Density, well-defined gluing and the limit norm
    bound have been proved separately. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseDaniellGluingConstruction InverseDaniellGluingLaws InverseLimitPullbackLattice
  InverseLimitPullbackDensity InverseLimitClosedCoordinate NormalizedProductSpace
  CompactDenseDaniellExtension CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_limit_daniell_integral_exists]: existence
    in the inverse-limit generalization of Federer 2.6.6,
    pp. 120–121, with the normalized monotone hypotheses
    retained. No countability or surjectivity is assumed. *)
Theorem inverse_limit_daniell_integral_exists (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_consistent_inverse_daniell_family le b A -> exists B, is_inverse_limit_daniell_integral p A B.
Proof.
move=> hs hl hA.
have [u0 _] := @normalized_daniell_product_nonempty R I Y A
  (@inverse_daniell_family_integral R I le Y b A hA) (@inverse_daniell_family_one R I le Y b A hA).
have [u hu] := compact_inverse_family_exists u0 hs.
have [x0 hx0] := compact_inverse_limit_realizes_family hl hu.
have [G hG] := @inverse_daniell_gluing_exists R I le Y b X p A u0 hs hl hA.
have hD := @inverse_limit_pullbacks_vector_lattice R I le Y b X p hs hl.
have hD1 := @inverse_limit_pullback_constant R I le Y b X p hs 1.
have hDK := @inverse_limit_pullback_membership R I le Y b X p hl.
have hden := @inverse_limit_pullbacks_uniformly_dense R I le Y b X p x0 hs hl.
have hlin := @inverse_daniell_glued_linear R I le Y b X p A G hs hl hA hG.
have h1 := @inverse_daniell_glued_one R I le Y b X p A G hs hA hG.
have hb := @inverse_daniell_glued_bound R I le Y b X p A G hs hl hA hG u0.
have [B [hB [hB1 hext]]] := @compact_dense_daniell_extension_exists R X _ G
  (compact_inverse_limit_hausdorff hl) (compact_inverse_limit_compact hl) hD hD1 hDK hden hlin h1 hb.
exists B; split=> //; split=> // i f hf.
have hDf : inverse_limit_pullbacks p (f \o p i) by exists i,f.
by rewrite (hext.1 _ hDf) (hG i f hf).
Qed.
