(** Federer (1969), 2.5.14, p. 107: the measurable open sets form a base,
    and a countable ambient base makes every open set measurable. General
    topology is proved separately from the measure laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP
  LocalizedCompactCutoffUP LocalizedCompactCutoff CompactSupportLevels FunctionLatticeUP
  FunctionLatticeLevelFamilies FunctionLatticeCountableLevels CountableOpenBaseUP CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_strict_levels_refine_open]: F0 supplies a
    neighborhood base in Federer 2.5.14, p. 107 A localized cutoff at the
    singleton gives a positive strict level contained in V. *)
Theorem compact_support_strict_levels_refine_open (R : realType) (X : topologicalType) :
  hausdorff_space X -> locally_compact (@setT X) ->
  forall V, open V -> forall x, V x -> exists U,
    function_lattice_strict_levels (@compactly_supported_continuous_functions R X) U /\ U x /\ U `<=` V.
Proof.
move=> hh hl V hV x hx.
have hKV : [set x] `<=` V by move=> y ->.
pose u := @localized_compact_cutoff R X [set x] V hh hl (@compact_set1 X x) hV hKV.
have hu := @localized_compact_cutoff_specification R X [set x] V hh hl (@compact_set1 X x) hV hKV.
have hcut := localized_compact_cutoff_laws hu.
pose U := [set y | (2 : R)^-1 < u y].
have ht : 0 < (2 : R)^-1 by rewrite invr_gt0 ltr0n.
have ht1 : (2 : R)^-1 < 1 by rewrite invf_lt1 // ltr1n.
exists U; split.
- exists u,(2 : R)^-1; split; last by split.
  split; first exact: compact_cutoff_function hcut.
  move=> y; exact: (andP (compact_cutoff_range hcut y)).1.
- split.
  + change (is_true ((2 : R)^-1 < u x)); rewrite /u (compact_cutoff_on_set hcut (erefl x)); exact ht1.
  + move=> y hy; apply: (localized_compact_cutoff_support hu).
    apply: subset_closure=> hz; change (is_true ((2 : R)^-1 < u y)) in hy.
    have hu0 : u y=0 := hz.
    by move: hy; rewrite hu0 ltNge (ltW ht).
Qed.

(** Source for [compact_support_open_is_increasing_level]: with a countable
    base, every open set belongs to F1 in Federer 2.5.14, p. 107 A countable
    subcover of basic strict levels gives the sequence. *)
Theorem compact_support_open_is_increasing_level (R : realType) (X : topologicalType)
    (B : nat -> set X) : hausdorff_space X -> locally_compact (@setT X) ->
  is_countable_open_base B -> forall V, open V ->
  function_lattice_increasing_levels (@compactly_supported_continuous_functions R X) V.
Proof.
move=> hh hl hB V hV.
pose C := [set U | function_lattice_strict_levels (@compactly_supported_continuous_functions R X) U /\ U `<=` V].
have ho U : C U -> open U by move=> [hU _]; exact: compact_support_strict_level_open hU.
have hc : V `<=` \bigcup_(U in C) U.
  move=> x hx; have [U [hU [hUx hUV]]] := @compact_support_strict_levels_refine_open R X hh hl V hV x hx.
  exists U=> //; by split.
have [G [hGC [hG hcG]]] := @countable_base_open_subcover X B V C hB ho hc.
have he : V=\bigcup_(U in G) U.
  apply/seteqP; split=> //; move=> x [U hU hx]; exact: (hGC U hU).2 x hx.
rewrite he; apply: (@function_lattice_countable_strict_levels_union R X _
  (@compactly_supported_continuous_functions_lattice R X) (fun _ => 0) G
  (@compactly_supported_zero_function R X) hG)=> U hU; exact: (hGC U hU).1.
Qed.
