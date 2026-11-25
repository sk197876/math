(** Federer (1969), 2.6.6, pp. 120–121: the union of coordinate pullbacks
    for a directed compact inverse limit. The vector-lattice laws follow
    from common upper indices and composition of the projections. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactInverseSystemUP CompactInverseLimitUP
  CompactContinuousPullback CompactSupportFunctionUP CompactUniformNorm
  DaniellSpaceCompactSpace FunctionLatticeUP VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_limit_pullbacks]: the directed union of
    coordinate pullbacks replacing L in the final paragraph of
    Federer 2.6.6, pp. 120–121. *)
Definition inverse_limit_pullbacks (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (X : topologicalType) (p : forall i, X -> Y i) : set (X -> R) :=
  [set g | exists i (f : Y i -> R), compactly_supported_continuous_functions f /\ g=f \o p i].

Section Pullbacks.
Variables (R : realType) (I : choiceType) (le : I -> I -> Prop).
Variables (Y : I -> topologicalType) (b : forall i j, Y j -> Y i).
Variables (X : topologicalType) (p : forall i, X -> Y i).
Arguments b i j _ : clear implicits.
Arguments p i _ : clear implicits.
Hypotheses (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p).
Local Notation L := (@inverse_limit_pullbacks R I Y X p).

(** Source for [inverse_limit_pullback_membership]: continuous
    coordinate functions pull back into K of the limit, supporting
    Federer 2.6.6, pp. 120–121. *)
Lemma inverse_limit_pullback_membership g : L g -> compactly_supported_continuous_functions g.
Proof.
move=> [i [f [hf ->]]]; exact (@compact_continuous_pullback_membership R X (Y i) (p i) f
  (compact_inverse_limit_compact hl) (@compact_inverse_limit_projection_continuous I le Y b X p hl i) hf).
Qed.

(** Source for [inverse_limit_pullback_common_stage]: two pullbacks
    can be represented at one upper index, supporting linearity
    and lattice closure in Federer 2.6.6, pp. 120–121. *)
Lemma inverse_limit_pullback_common_stage g h : L g -> L h ->
  exists k (f t : Y k -> R), compactly_supported_continuous_functions f /\
    compactly_supported_continuous_functions t /\ g=f \o p k /\ h=t \o p k.
Proof.
move=> [i [f [hf ->]]] [j [t [ht ->]]].
have [k [hik hjk]] := directed_preorder_upper (compact_inverse_system_directed hs) i j.
exists k, (f \o b i k), (t \o b j k); split.
- exact (@compact_continuous_pullback_membership R (Y k) (Y i) (b i k) f
    (@compact_inverse_system_compact I le Y b hs k) (@compact_inverse_system_continuous I le Y b hs i k hik) hf).
split.
- exact (@compact_continuous_pullback_membership R (Y k) (Y j) (b j k) t
    (@compact_inverse_system_compact I le Y b hs k) (@compact_inverse_system_continuous I le Y b hs j k hjk) ht).
split; apply: funext=> x; rewrite /=.
- by rewrite (@compact_inverse_limit_projection_compatible I le Y b X p hl x i k hik).
- by rewrite (@compact_inverse_limit_projection_compatible I le Y b X p hl x j k hjk).
Qed.

(** Source for [inverse_limit_pullback_constant]: constants belong
    to the coordinate pullback union in Federer 2.6.6,
    pp. 120–121, since the directed index set is nonempty. *)
Lemma inverse_limit_pullback_constant (c : R) : L (fun _=>c).
Proof.
have [i _] := directed_preorder_nonempty (compact_inverse_system_directed hs).
exists i, (fun _=>c); split=> //.
split; first exact (@cst_continuous (Y i) (real_line_metric R) c).
exact: subclosed_compact (@real_function_support_closed R (Y i) _) (@compact_inverse_system_compact I le Y b hs i) (@subsetT _ _).
Qed.

(** Source for [inverse_limit_pullback_scale]: scalar closure
    of the directed union, supporting Federer 2.6.6, pp. 120–121. *)
Lemma inverse_limit_pullback_scale c g : L g -> L (fun x=>c*g x).
Proof.
move=> [i [f [hf ->]]]; exists i, (fun y=>c*f y); split=> //.
exact: (@compact_support_vector_lattice R (Y i)).2.2 c f hf.
Qed.

(** Source for [inverse_limit_pullback_binary]: pointwise binary
    operations preserving each K also preserve the directed union,
    supporting Federer 2.6.6, pp. 120–121. *)
Lemma inverse_limit_pullback_binary (u : R -> R -> R) g h :
  (forall i (f t : Y i -> R), compactly_supported_continuous_functions f ->
    compactly_supported_continuous_functions t -> compactly_supported_continuous_functions (fun y=>u (f y) (t y))) ->
  L g -> L h -> L (fun x=>u (g x) (h x)).
Proof.
move=> hu hg hh; have [k [f [t [hf [ht [-> ->]]]]]] := inverse_limit_pullback_common_stage hg hh.
exists k, (fun y=>u (f y) (t y)); split=> //; exact: hu.
Qed.

(** Source for [inverse_limit_pullbacks_vector_lattice]: the
    directed pullback union is a vector lattice, as required to
    repeat the extension argument in Federer 2.6.6, pp. 120–121. *)
Theorem inverse_limit_pullbacks_vector_lattice : is_vector_function_lattice L.
Proof.
split.
- constructor.
  + move=> g h; apply: inverse_limit_pullback_binary=> i f t hf ht.
    exact: (@function_lattice_add R (Y i) _ (@compact_support_vector_lattice R (Y i)).1 f t hf ht).
  + move=> c g hc; exact: inverse_limit_pullback_scale.
  + move=> g h; apply: inverse_limit_pullback_binary=> i f t hf ht.
    exact: (@function_lattice_minimum R (Y i) _ (@compact_support_vector_lattice R (Y i)).1 f t hf ht).
  + move=> c g hc hg; apply: (@inverse_limit_pullback_binary (fun a b=>Order.min a b) g (fun _=>c))=> //.
    * move=> i f t hf ht; exact: (@function_lattice_minimum R (Y i) _ (@compact_support_vector_lattice R (Y i)).1 f t hf ht).
    * exact: inverse_limit_pullback_constant.
  + move=> g h hg hh hgh; apply: (@inverse_limit_pullback_binary (fun a b=>a-b) h g)=> // i f t hf ht.
    exact: (@vector_function_lattice_difference R (Y i) _ (@compact_support_vector_lattice R (Y i)) f t hf ht).
- split; [exact: inverse_limit_pullback_constant|exact: inverse_limit_pullback_scale].
Qed.
End Pullbacks.
