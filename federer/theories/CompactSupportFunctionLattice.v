(** Federer (1969), 2.5.13, p. 106: the compactly supported continuous real
    functions form the function lattice L. Closure of supports is proved
    inside the project; continuity of the elementary operations is reused
    from the earlier 2.5.1 lattice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground FunctionLatticeUP ContinuousFunctionLattice CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_unary_operation]: supporting
    closure of supports under operations preserving zero for the
    lattice in Federer 2.5.13, p. 106. *)
Lemma compact_support_unary_operation (R : realType) (X : topologicalType) (f g : X -> R) :
  compact (real_function_support f) -> (forall x, f x=0 -> g x=0) -> compact (real_function_support g).
Proof.
move=> hf he; apply: (@real_function_compact_support_in_closed_set R X g (real_function_support f)
  hf (@real_function_support_closed R X f))=> x hx.
apply: he; exact: real_function_zero_off_support hx.
Qed.

(** Source for [compact_support_binary_operation]: supporting
    finite-union bound on supports for the lattice in Federer
    2.5.13, p. 106; no separation assumption is needed. *)
Lemma compact_support_binary_operation (R : realType) (X : topologicalType) (f g h : X -> R) :
  compact (real_function_support f) -> compact (real_function_support g) ->
  (forall x, f x=0 -> g x=0 -> h x=0) -> compact (real_function_support h).
Proof.
move=> hf hg he; apply: (@real_function_compact_support_in_closed_set R X h
  (real_function_support f `|` real_function_support g)).
- exact: compactU hf hg.
- exact: closedU (@real_function_support_closed R X f) (@real_function_support_closed R X g).
- move=> x hx; apply: he.
  + apply: real_function_zero_off_support=> hf'; apply: hx; by left.
  + apply: real_function_zero_off_support=> hg'; apply: hx; by right.
Qed.

(** Source for [compactly_supported_zero_function]: nonempty-
    lattice and empty-support case in Federer 2.5.13, p. 106.
    This includes an empty ambient topological space. *)
Lemma compactly_supported_zero_function (R : realType) (X : topologicalType) :
  compactly_supported_continuous_functions (fun _ : X => (0 : R)).
Proof.
split; first by move=> x; exact: cvg_cst.
have he : [set x : X | (0 : R) <> 0] = set0 by apply/seteqP; split=> x; by [].
rewrite /real_function_support he closure0; exact: compact0.
Qed.

(** Source for [compactly_supported_continuous_functions_lattice]: direct
    verification that L in Federer 2.5.13, p. 106, satisfies the
    function-lattice laws of 2.5.1, p. 91 Local compactness and Hausdorff
    separation are only needed later for cutoffs. *)
Theorem compactly_supported_continuous_functions_lattice (R : realType) (X : topologicalType) :
  is_function_lattice (@compactly_supported_continuous_functions R X).
Proof.
have hL := @continuous_functions_lattice R X.
constructor.
- move=> f g [hf hs] [hg ht]; split.
  + exact (@function_lattice_add R X _ hL f g hf hg).
  + apply: (@compact_support_binary_operation R X f g _ hs ht)=> x -> ->; exact: add0r.
- move=> c f hc [hf hs]; split.
  + exact (@function_lattice_scale R X _ hL c f hc hf).
  + apply: (@compact_support_unary_operation R X f _ hs)=> x ->; exact: mulr0.
- move=> f g [hf hs] [hg ht]; split.
  + exact (@function_lattice_minimum R X _ hL f g hf hg).
  + apply: (@compact_support_binary_operation R X f g _ hs ht)=> x -> ->; exact: minxx.
- move=> c f hc [hf hs]; split.
  + exact (@function_lattice_truncation R X _ hL c f hc hf).
  + apply: (@compact_support_unary_operation R X f _ hs)=> x ->; by rewrite (min_idPl hc).
- move=> f g [hf hs] [hg ht] hfg; split.
  + exact (@function_lattice_ordered_difference R X _ hL f g hf hg hfg).
  + apply: (@compact_support_binary_operation R X f g _ hs ht)=> x -> ->; exact: subrr.
Qed.
