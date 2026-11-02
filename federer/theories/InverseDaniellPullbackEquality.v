(** Federer (1969), 2.6.6, pp. 120–121: agreement of the factor integrals
    whenever their pullbacks to the limit are equal. This justifies the
    gluing in the inverse-limit paragraph without surjectivity. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseDaniellPullbackBound CompactContinuousPullback CompactSupportFunctionUP
  CompactUniformNorm UniformFunctionNorm UniformFunctionNormUP UniformFunctionNormLaws
  DaniellSpaceCompactness MonotoneDaniellIntegralSum VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_daniell_pullback_equal]: equality of the
    proposed integral for two presentations of a pullback in the
    inverse-limit extension of Federer 2.6.6, pp. 120–121. *)
Theorem inverse_daniell_pullback_equal (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) (u0 : prod_topology Y) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_consistent_inverse_daniell_family le b A -> forall i j (f : Y i -> R) (g : Y j -> R),
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
  f \o p i=g \o p j -> A i f=A j g.
Proof.
move=> hs hl hA i j f g hf hg he.
have [k [hik hjk]] := directed_preorder_upper (compact_inverse_system_directed hs) i j.
pose fk := f \o b i k; pose gk := g \o b j k.
have hfk := @compact_continuous_pullback_membership R (Y k) (Y i) (b i k) f
  (@compact_inverse_system_compact I le Y b hs k) (@compact_inverse_system_continuous I le Y b hs i k hik) hf.
have hgk := @compact_continuous_pullback_membership R (Y k) (Y j) (b j k) g
  (@compact_inverse_system_compact I le Y b hs k) (@compact_inverse_system_continuous I le Y b hs j k hjk) hg.
pose d := fun y=>fk y-gk y.
have hd := @vector_function_lattice_difference R (Y k) _ (@compact_support_vector_lattice R (Y k)) fk gk hfk hgk.
have hd0 : d \o p k=(fun _ : X=>0).
  apply: funext=> x; rewrite /d /fk /gk /=
    (@compact_inverse_limit_projection_compatible I le Y b X p hl x i k hik)
    (@compact_inverse_limit_projection_compatible I le Y b X p hl x j k hjk).
  have hx := congr1 (fun t=>t x) he; rewrite /= in hx; by rewrite hx subrr.
have hb := @inverse_daniell_pullback_norm_bound R I le Y b X p A u0 hs hl hA k d hd.
have hdp := @compact_continuous_pullback_membership R X (Y k) (p k) d
  (compact_inverse_limit_compact hl) (@compact_inverse_limit_projection_continuous I le Y b X p hl k) hd.
have hn := compact_support_uniform_norm_specification hdp.
rewrite hd0 in hb hn.
have hzero := uniform_function_norm_unique hn (@uniform_function_norm_zero R X).
rewrite hzero normr_le0 in hb.
have hlin := @daniell_compact_support_linear R (Y k) (A k)
  (monotone_daniell_integral_is_daniell (@inverse_daniell_family_integral R I le Y b A hA k)).
have hdiff := @vector_lattice_additive_difference R (Y k) _ (A k)
  (@compact_support_vector_lattice R (Y k)) hlin.1 fk gk hfk hgk.
move: hb; rewrite hdiff subr_eq0=> /eqP hk.
rewrite -(@inverse_daniell_family_consistent R I le Y b A hA i k hik f hf)
  -(@inverse_daniell_family_consistent R I le Y b A hA j k hjk g hg).
exact: hk.
Qed.
