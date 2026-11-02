(** Federer (1969), 2.6.6, pp. 120–121: actual density of the coordinate
    pullbacks for a compact Hausdorff inverse limit. Point separation gives
    two-point interpolation, and the proved compact lattice approximation
    supplies uniform density. Supporting source: Kelley 7.R(a), pp. 244–245,
    Dover 2017 reprint of 1955. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP
  InverseLimitPullbackLattice CompactLatticeInterpolation CompactTwoPointInterpolation
  CompactUniformNorm UniformFunctionNorm CompactSupportFunctionUP FunctionSeminormDistance
  ScalarLipschitzExtensionUP VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_limit_pullbacks_interpolate]: two-point
    interpolation by coordinate pullbacks, supporting the density
    used in Federer 2.6.6, pp. 120–121. *)
Lemma inverse_limit_pullbacks_interpolate (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i) (f : X -> R) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  forall x y, exists g, inverse_limit_pullbacks p g /\ g x=f x /\ g y=f y.
Proof.
move=> hs hl x y; case: (eqVneq x y)=> [<-|hxy].
- exists (fun _=>f x); split; first exact (@inverse_limit_pullback_constant R I le Y b X p hs (f x)).
  by split.
- have hsep : exists i, p i x != p i y.
    apply: contrapT=> hn; have he : x=y.
      apply: (@compact_inverse_limit_separates I le Y b X p hl x y)=> i.
      apply: contrapT=> hne; apply: hn; exists i.
      apply/negP=> /eqP he; exact: hne he.
    by move: hxy; rewrite he eqxx.
  have [i hi] := hsep.
  have [g [hg [hx hy]]] := @compact_two_point_interpolation R (Y i) (p i x) (p i y) (f x) (f y)
    (@compact_inverse_system_hausdorff I le Y b hs i) (@compact_inverse_system_compact I le Y b hs i) hi.
  exists (g \o p i); split; last by split.
  by exists i,g.
Qed.

(** Source for [inverse_limit_pullbacks_uniformly_dense]: proved
    uniform density needed to apply the finite-to-infinite reasoning
    to arbitrary compact inverse limits in Federer 2.6.6,
    pp. 120–121. Density is a conclusion, not an added axiom. *)
Theorem inverse_limit_pullbacks_uniformly_dense (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i) (x0 : X) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_pseudometric_dense_subset (@compactly_supported_continuous_functions R X)
    (@inverse_limit_pullbacks R I Y X p)
    (function_seminorm_distance (@compact_support_uniform_norm R X)).
Proof.
move=> hs hl f hf e he.
have hL := @inverse_limit_pullbacks_vector_lattice R I le Y b X p hs hl.
have hLK := @inverse_limit_pullback_membership R I le Y b X p hl.
have [g [hg hnear]] := @compact_lattice_two_point_density R X _ x0 f e
  (compact_inverse_limit_compact hl) hL.1 (fun g hg=>(hLK g hg).1) hf.1 he
  (@inverse_limit_pullbacks_interpolate R I le Y b X p f hs hl).
exists g; split=> //.
apply: compact_support_uniform_norm_strict_bound=> //.
exact: (@vector_function_lattice_difference R X _ (@compact_support_vector_lattice R X) f g hf (hLK g hg)).
Qed.
