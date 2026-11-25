(** Federer (1969), 2.6.6, pp. 120–121: the glued inverse-limit functional
    is linear, normalized, and bounded by the uniform norm. Proofs use only
    its agreement laws, keeping the choice of a presentation private. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseDaniellPullbackBound InverseLimitPullbackLattice CompactContinuousPullback
  CompactSupportFunctionUP CompactUniformNorm UniformFunctionNorm DaniellSpaceCompactSpace
  DaniellSpaceCompactness MonotoneDaniellIntegralSum FunctionLatticeUP FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Glued.
Variables (R : realType) (I : choiceType) (le : I -> I -> Prop).
Variables (Y : I -> topologicalType) (b : forall i j, Y j -> Y i).
Variables (X : topologicalType) (p : forall i, X -> Y i).
Variables (A : forall i, (Y i -> R) -> R) (G : (X -> R) -> R).
Arguments b i j _ : clear implicits.
Arguments p i _ : clear implicits.
Hypotheses (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A).
Hypothesis hG : forall i (f : Y i -> R), compactly_supported_continuous_functions f -> G (f \o p i)= @A i f.

(** Source for [inverse_daniell_glued_linear]: linearity of
    the glued functional in the inverse-limit argument of
    Federer 2.6.6, pp. 120–121. *)
Theorem inverse_daniell_glued_linear :
  is_linear_functional_on_functions (@inverse_limit_pullbacks R I Y X p) G.
Proof.
split.
- move=> g h hg hh.
  have [k [f [t [hf [ht [-> ->]]]]]] := @inverse_limit_pullback_common_stage R I le Y b X p hs hl g h hg hh.
  have hsum := @function_lattice_add R (Y k) _ (@compact_support_vector_lattice R (Y k)).1 f t hf ht.
  change (G ((fun y=>f y+t y) \o p k)=G (f \o p k)+G (t \o p k)).
  rewrite (@hG k _ hsum) (@hG k _ hf) (@hG k _ ht).
  exact: (@daniell_compact_support_linear R (Y k) (@A k)
    (monotone_daniell_integral_is_daniell (@inverse_daniell_family_integral R I le Y b A hA k))).1 f t hf ht.
- move=> c g [i [f [hf ->]]].
  have hcf := (@compact_support_vector_lattice R (Y i)).2.2 c f hf.
  change (G ((fun y=>c*f y) \o p i)=c*G (f \o p i)).
  rewrite (@hG i _ hcf) (@hG i _ hf).
  exact: (@daniell_compact_support_linear R (Y i) (@A i)
    (monotone_daniell_integral_is_daniell (@inverse_daniell_family_integral R I le Y b A hA i))).2 c f hf.
Qed.

(** Source for [inverse_daniell_glued_one]: normalization of
    the inverse-limit functional, retaining the hypotheses of
    Federer 2.6.6, p. 120. *)
Lemma inverse_daniell_glued_one : G (fun _=>1) = 1.
Proof.
have [i _] := directed_preorder_nonempty (compact_inverse_system_directed hs).
have h1 := @compact_space_constant_one R (Y i) (@compact_inverse_system_compact I le Y b hs i).
have he := @hG i _ h1.
rewrite (@inverse_daniell_family_one R I le Y b A hA i) in he; exact: he.
Qed.

(** Source for [inverse_daniell_glued_bound]: |gamma|<=nu
    on the directed pullback union in the inverse-limit extension
    of Federer 2.6.6, pp. 120–121. *)
Lemma inverse_daniell_glued_bound (u0 : prod_topology Y) :
  forall g, inverse_limit_pullbacks p g -> `|G g|<=compact_support_uniform_norm g.
Proof.
move=> g [i [f [hf ->]]]; rewrite (@hG i f hf).
exact: (@inverse_daniell_pullback_norm_bound R I le Y b X p A u0 hs hl hA i f hf).
Qed.
End Glued.
