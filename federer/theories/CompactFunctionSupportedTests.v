(** Federer (1969), 2.5.20, p. 114: countably many tests suffice for the
    inferred support inclusion. The tests below are uniformly dense among
    the functions whose compact support lies inside a prescribed open set.
    Localized cutoffs, from 2.5.14, p. 108, ensure their nonzero loci cover
    that open set. Source context: CompactFunctionSpaceUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionSpace
  CompactFunctionSubsetApproximation CompactSupportFunctionUP CountableOpenBaseUP
  CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_countable_supported_test_family]: supporting
    countable uniform tests for the support assertion in Federer
    2.5.20, p. 114. Compact supports, rather than merely
    nonzero loci, lie in U. *)
Record is_countable_supported_test_family (R : realType) (Y : topologicalType)
    (U : set Y) (D : set (Y -> R)) : Prop := {
  (** Source for [supported_tests_countable]: countability
      needed for a common exceptional null set, supporting
      Federer 2.5.20, p. 114. *)
  supported_tests_countable : countable D;
  (** Source for [supported_tests_member]: the tests are
      members of K(Y) supported in U, supporting the support
      assertion in Federer 2.5.20, p. 114. *)
  supported_tests_member : forall f, D f ->
    compactly_supported_continuous_functions f /\ real_function_support f `<=` U;
  (** Source for [supported_tests_approximate]: uniform
      approximation by the countable tests, supporting the
      support assertion in Federer 2.5.20, p. 114. *)
  supported_tests_approximate : forall f,
    compactly_supported_continuous_functions f -> real_function_support f `<=` U ->
    forall e : R, 0<e -> exists g, D g /\ forall y, `|f y-g y|<e
}.

(** Source for [countable_supported_test_family_exists]:
    countable uniform tests exist by separability of K(Y),
    supporting the support conclusion of Federer 2.5.20,
    p. 114. No closedness of the supported-function class
    is needed. *)
Theorem countable_supported_test_family_exists (R : realType) (Y : topologicalType)
    (B : nat -> set Y) (U : set Y) :
  compact (@setT Y) -> is_countable_open_base B ->
  exists D : set (Y -> R), is_countable_supported_test_family U D.
Proof.
move=> hY hB.
pose E := compact_function_space R Y.
pose ev := @compact_function_evaluate R Y.
have hE := @compact_function_space_specification R Y.
pose S : set E := [set v | real_function_support (ev v) `<=` U].
have [D [hD [hDS hdense]]] := @compact_function_subset_countable_approximation R Y E ev hE B S hY hB.
exists (ev @` D); constructor.
- exact: sub_countable (card_image_le _ _) hD.
- move=> f [v hv <-]; split; first exact: (@compact_function_evaluation_member R Y E ev hE v).
  exact: hDS v hv.
- move=> f hf hs e he; have [v hev] := compact_function_evaluation_surjective hE hf.
  have hev' : ev v=f := hev.
  have hSv : S v.
    change (real_function_support (ev v) `<=` U); by rewrite hev'.
  have [u [hu hb]] := hdense v hSv e he.
  exists (ev u); split; first by exists u.
  move=> y.
  have hbound := compact_function_evaluation_bound hE (v-u) y.
  rewrite (compact_function_evaluation_subtract hE) in hbound.
  rewrite -hev'; exact: le_lt_trans hbound hb.
Qed.

(** Source for [supported_tests_cover_open_set]: every point
    of U belongs to the nonzero locus of one countable test,
    supporting the support conclusion in Federer 2.5.20,
    p. 114. This follows by approximating a cutoff equal
    to one at that point. *)
Theorem supported_tests_cover_open_set (R : realType) (Y : topologicalType)
    (U : set Y) (D : set (Y -> R)) :
  hausdorff_space Y -> locally_compact (@setT Y) -> open U ->
  is_countable_supported_test_family U D -> forall y, U y -> exists f, D f /\ f y<>0.
Proof.
move=> hh hl hU hD y hy.
have hsub : [set y] `<=` U by move=> z ->.
pose f := @localized_compact_cutoff R Y [set y] U hh hl (@compact_set1 Y y) hU hsub.
have hf := @localized_compact_cutoff_specification R Y [set y] U hh hl (@compact_set1 Y y) hU hsub.
have hfK := compact_cutoff_function (localized_compact_cutoff_laws hf).
have hfS := @localized_compact_cutoff_support R Y [set y] U f hf.
have he : (0 : R)<1/2 by rewrite divr_gt0 // ltr0n.
have [g [hg hnear]] := @supported_tests_approximate R Y U D hD f hfK hfS (1/2) he.
exists g; split=> // hg0.
have h := hnear y.
have hfy : f y= 1 := compact_cutoff_on_set (localized_compact_cutoff_laws hf) (erefl y).
change (is_true (`|f y-g y|<1/2)) in h.
rewrite hfy hg0 subr0 normr1 in h.
have hhalf : (1/2 : R)<1 by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
lra.
Qed.
