(** General-topology support for Federer (1969), 2.6.6, pp. 120–121: compact
    Hausdorff spaces admit continuous two-point interpolation. The localized
    cutoff already used in 2.5.14 gives the function. This supplies the
    hypothesis of Kelley, General Topology, Chapter 7 Problem R(a), pp.
    244–245 (Dover 2017 reprint of 1955), rather than importing a
    Stone–Weierstrass theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactCutoffUP LocalizedCompactCutoffUP
  LocalizedCompactCutoff SubtypeCompactHausdorff CompactUniformNorm FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_two_point_interpolation]: general-topology
    interpolation supporting the density in Federer 2.6.6,
    pp. 120–121; Kelley 7.R(a), pp. 244–245. Distinct
    points may be assigned arbitrary finite real values. *)
Theorem compact_two_point_interpolation (R : realType) (X : topologicalType)
    (x y : X) (a b : R) : hausdorff_space X -> compact (@setT X) -> x != y ->
  exists f : X -> R, compactly_supported_continuous_functions f /\ f x=a /\ f y=b.
Proof.
move=> hh hc hxy.
have hy : closed [set y] := compact_closed hh (@compact_set1 X y).
have ho : open (~` [set y]) := closed_openC hy.
have hsub : [set x] `<=` ~` [set y].
  move=> z -> he; move: hxy; by rewrite he eqxx.
pose u := @localized_compact_cutoff R X [set x] (~` [set y]) hh
  (compact_space_locally_compact hc) (@compact_set1 X x) ho hsub.
have hu := @localized_compact_cutoff_specification R X [set x] (~` [set y]) hh
  (compact_space_locally_compact hc) (@compact_set1 X x) ho hsub.
have hux : u x = 1 := compact_cutoff_on_set (localized_compact_cutoff_laws hu) (erefl x).
have huy : u y=0.
  apply: real_function_zero_off_support=> hs.
  have hn : (~` [set y]) y := @localized_compact_cutoff_support R X [set x] (~` [set y]) u hu y hs.
  exact: hn (erefl y).
have hb : compactly_supported_continuous_functions (fun _ : X=>b).
  split; first by move=> z; exact: cvg_cst.
  exact: subclosed_compact (@real_function_support_closed R X _) hc (@subsetT _ _).
exists (fun z=>b+(a-b)*u z); split.
- exact: (@function_lattice_add R X _ (@compact_support_vector_lattice R X).1 _ _ hb
    ((@compact_support_vector_lattice R X).2.2 (a-b) u
      (compact_cutoff_function (localized_compact_cutoff_laws hu)))).
split; rewrite ?hux ?huy ?mulr1 ?mulr0 ?addr0; first by rewrite addrC subrK.
by [].
Qed.
