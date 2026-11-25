(** Federer (1969), 2.5.13, pp. 106–107: a linear functional on K(X) which
    is bounded above on positive order intervals is Daniell. Monotonicity
    supplies those bounds, as used for the finite marginals in 2.6.6, p.
    120. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportRieszRepresentation FunctionLatticeUP
  FunctionLatticeSeminormUP DaniellIntegralUP MonotoneDaniellIntegralUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monotone_compact_support_linear_daniell]: supporting
    consequence of Federer 2.5.13, p. 106, applied to the
    finite marginal functionals in 2.6.6, p. 120. Local compactness
    suffices; compactness of the whole space is not needed. *)
Theorem monotone_compact_support_linear_daniell (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R X) A ->
  (forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    function_le f g -> A f<=A g) ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A.
Proof.
move=> hh hl hlin hmono.
have hD : is_daniell_integral (@compactly_supported_continuous_functions R X) A.
  apply: (@compact_support_order_bounded_daniell R X A hh hl hlin)=> u hu.
  exists (A u)=> f [hf [hf0 hfu]]; exact: hmono f u hf hu.1 hfu.
constructor.
- exact: daniell_integral_add hD.
- exact: daniell_integral_scale hD.
- exact: hmono.
- move=> f g hf hg hi; split.
  + move=> n m hnm; rewrite lee_fin; apply: (@hmono (f n) (f m) (hf n) (hf m))=> x.
    exact: (hi x).1 n m hnm.
  + exact: (@daniell_integral_increasing_continuity R X _ A hD f g hf hg hi).
Qed.
