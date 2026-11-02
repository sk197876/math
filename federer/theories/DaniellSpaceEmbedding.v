(** Federer (1969), 2.5.19, p. 113, second paragraph: for a locally compact
    Hausdorff space X and L = K(X), the map delta embeds X homeomorphically
    in K(X)*, and for every closed subset S of X the set K(X)* ∩ {mu : spt
    mu ⊂ S} is relatively closed in K(X)*. The support of a Daniell integral
    is that of 2.5.14, p. 108. The embedding is expressed by continuity,
    injectivity and openness onto the image; the relative closedness states
    that a Daniell integral in the closure of the set has its support in S.
    A supporting lemma shows that a Daniell integral on K(X) vanishes on
    every member of K(X) whose support misses the support of the integral,
    by the finite partitions of unity of 2.5.14. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellIntegralAlgebra CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportProducts CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff
  CompactFiniteCover FiniteCompactPartitionUP FiniteCompactPartitionSealed
  CompactSupportDaniellSupport DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lattice_finite_sum_member]: finite sums of members of a
    lattice containing zero belong to the lattice, by the addition clause
    of Federer 2.5.1, p. 91; supporting 2.5.19, p. 113. *)
Lemma lattice_finite_sum_member (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (I : eqType) (s : seq I) (k : I -> X -> R) :
  L (fun _ => 0) -> (forall i, i \in s -> L (k i)) -> L (fun x => \sum_(i <- s) k i x).
Proof.
move=> h0 hk; elim: s hk=> [|i s ih] hk.
- have -> : (fun x : X => \sum_(j <- [::]) k j x) = (fun _ => 0).
    by apply: funext=> x; rewrite big_nil.
  exact: h0.
- have -> : (fun x : X => \sum_(j <- i :: s) k j x) = (fun x => k i x + \sum_(j <- s) k j x).
    by apply: funext=> x; rewrite big_cons.
  apply: (function_lattice_add hL (hk i (mem_head i s))); apply: ih=> j hj; apply: hk.
  by rewrite in_cons hj orbT.
Qed.

(** Source for [daniell_finite_sum]: a Daniell integral is additive on
    finite sums of members of its lattice, by the first hypothesis of
    Federer 2.5.5, p. 96; supporting 2.5.19, p. 113. *)
Lemma daniell_finite_sum (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (I : eqType) (s : seq I) (k : I -> X -> R) :
  L (fun _ => 0) -> (forall i, i \in s -> L (k i)) ->
  A (fun x => \sum_(i <- s) k i x) = \sum_(i <- s) A (k i).
Proof.
move=> h0 hk; elim: s hk=> [|i s ih] hk.
- have -> : (fun x : X => \sum_(j <- [::]) k j x) = (fun _ => 0).
    by apply: funext=> x; rewrite big_nil.
  by rewrite big_nil; exact: (daniell_integral_zero hA h0).
- have -> : (fun x : X => \sum_(j <- i :: s) k j x) = (fun x => k i x + \sum_(j <- s) k j x).
    by apply: funext=> x; rewrite big_cons.
  have hk' : forall j, j \in s -> L (k j) by move=> j hj; apply: hk; rewrite in_cons hj orbT.
  by rewrite (daniell_integral_add hA (hk i (mem_head i s)) (lattice_finite_sum_member hL h0 hk'))
    (ih hk') big_cons.
Qed.

Section Embedding.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hh : hausdorff_space X.
Hypothesis hl : locally_compact (@setT X).
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [point_cutoff]: a member of K(X) with value one at a
    point and support in a given open neighbourhood, from the localised
    cutoff of Federer 2.5.14, p. 108; supporting the embedding of
    2.5.19, p. 113. *)
Lemma point_cutoff (x : X) (U : set X) :
  open U -> U x ->
  exists f : X -> R, compactly_supported_continuous_functions f /\
    (forall y, 0 <= f y <= 1) /\ f x = 1 /\ real_function_support f `<=` U.
Proof.
move=> hU hx.
have hKU : [set x] `<=` U by move=> y ->.
have hs := @localized_compact_cutoff_specification R X [set x] U hh hl (@compact_set1 X x) hU hKU.
exists (@localized_compact_cutoff R X [set x] U hh hl (@compact_set1 X x) hU hKU).
have hc := localized_compact_cutoff_laws hs.
split; first exact: (compact_cutoff_function hc).
split; first exact: (compact_cutoff_range hc).
split; first exact (compact_cutoff_on_set hc (x := x) erefl).
exact: (localized_compact_cutoff_support hs).
Qed.

(** Source for [point_evaluation_injective]: delta is injective on a
    locally compact Hausdorff space, part of the embedding statement of
    Federer 2.5.19, p. 113. *)
Lemma point_evaluation_injective (x y : X) :
  @point_evaluation R X x = @point_evaluation R X y -> x = y.
Proof.
move=> hxy; apply: contrapT=> hne.
have hU : open (~` [set y]) by rewrite openC; exact: compact_closed hh (@compact_set1 X y).
have hx : (~` [set y]) x by move=> hxy'; exact: hne hxy'.
have [f [hf [hr [hfx hsupp]]]] := point_cutoff hU hx.
have hfy : f y = 0 by apply: real_function_zero_off_support=> hy; exact: hsupp y hy erefl.
have := congr1 (fun T : (X -> R) -> R => T f) hxy.
rewrite /point_evaluation /= hfx hfy=> /eqP.
by rewrite oner_eq0.
Qed.

(** Source for [point_evaluation_continuous_compact_support]: delta is
    continuous into K(X)*, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_continuous_compact_support :
  continuous (@point_evaluation R X : X -> daniell_weak_space K).
Proof. by apply: point_evaluation_continuous=> f hf; exact: hf.1. Qed.

(** Source for [point_evaluation_open_image]: delta is open onto its
    image: for every open set U and x in U there is an open subset V of K(X)*
    containing delta_x such that delta_y in V implies y in U; with
    continuity and injectivity this is the homeomorphic embedding of
    Federer 2.5.19, p. 113. *)
Theorem point_evaluation_open_image (U : set X) (x : X) :
  open U -> U x ->
  exists V : set (daniell_weak_space K), open V /\ V (@point_evaluation R X x) /\
    forall y, V (@point_evaluation R X y) -> U y.
Proof.
move=> hU hx; have [f [hf [hr [hfx hsupp]]]] := point_cutoff hU hx.
exists [set A : daniell_weak_space K | 1 / 2 < A f /\ A f < 2].
split; first exact: daniell_weak_strip_open hf.
split; first by rewrite /point_evaluation /= hfx; split; lra.
move=> y [h1 h2]; rewrite /point_evaluation /= in h1 h2.
apply: hsupp; apply: subset_closure=> hfy.
by rewrite hfy in h1; lra.
Qed.

(** Source for [point_evaluation_homeomorphic_embedding]: the three
    properties of delta forming the homeomorphic embedding of X in K(X)*
    stated in Federer 2.5.19, p. 113. *)
Theorem point_evaluation_homeomorphic_embedding :
  continuous (@point_evaluation R X : X -> daniell_weak_space K) /\
  (forall x y, @point_evaluation R X x = @point_evaluation R X y -> x = y) /\
  (forall U x, open U -> U x ->
    exists V : set (daniell_weak_space K), open V /\ V (@point_evaluation R X x) /\
      forall y, V (@point_evaluation R X y) -> U y).
Proof.
split; first exact: point_evaluation_continuous_compact_support.
split; first exact: point_evaluation_injective.
exact: point_evaluation_open_image.
Qed.

(** Source for [daniell_support_vanishing]: Supporting Federer 2.5.14, p;
    supporting the relative closedness of Federer 2.5.19, p. 113. *)
Lemma daniell_support_vanishing (A : (X -> R) -> R) (f : X -> R) :
  is_daniell_integral K A -> compactly_supported_continuous_functions f ->
  real_function_support f `<=` ~` compact_support_daniell_support A -> A f = 0.
Proof.
move=> hA hf hsub.
pose C := [set W : set X | open W /\ forall g, compactly_supported_continuous_functions g ->
  real_function_support g `<=` W -> A g = 0].
have hcov : real_function_support f `<=` \bigcup_(W in C) W.
  by move=> x hx; have := hsub x hx; rewrite /compact_support_daniell_support setCK.
have hC : forall W, C W -> open W by move=> W [hW _].
have [F hFC hFK] := @compact_open_finite_cover X [the choiceType of set X] C id
  (real_function_support f) hf.2 hC hcov.
have hF W : W \in F -> open W.
  by move=> hW; apply: hC; exact: set_mem (hFC W hW).
pose g := @FiniteCompactPartition.value R X [the choiceType of set X] id F
  (real_function_support f) hh hl hf.2 hF hFK.
have hg := @FiniteCompactPartition.laws R X [the choiceType of set X] id F
  (real_function_support f) hh hl hf.2 hF hFK.
pose k := fun W x => f x * g W x.
have hk : forall W, W \in F -> compactly_supported_continuous_functions (k W).
  move=> W hW.
  exact: (compact_support_continuous_multiplier hf.1 (finite_compact_partition_functions hg hW)).
have hkz : forall W, W \in F -> A (k W) = 0.
  move=> W hW; have hCW : C W := set_mem (hFC W hW).
  apply: hCW.2 (hk W hW) _.
  have h1 := @real_product_support_right R X f (g W).
  have h2 := finite_compact_partition_support hg hW.
  by rewrite /k=> y hy; apply: h2; apply: h1.
have he : f = (fun x => \sum_(W <- F) k W x).
  apply: funext=> x; rewrite /k -mulr_sumr.
  case: (pselect (real_function_support f x))=> hx.
  + by rewrite (finite_compact_partition_sum hg hx) mulr1.
  + by rewrite (real_function_zero_off_support hx) mul0r.
have hL := @compactly_supported_continuous_functions_lattice R X.
have h0 : compactly_supported_continuous_functions (fun _ : X => (0 : R)) :=
  @compactly_supported_zero_function R X.
rewrite [X in A X = _]he (daniell_finite_sum hL hA h0 hk) big_seq.
by apply: big1=> W hW; exact: hkz.
Qed.

(** Source for [daniell_support_relatively_closed]: for a closed subset
    S of X, a Daniell integral on K(X) lying in the closure of
    K(X)* ∩ {mu : spt mu ⊂ S} has its support in S; this is the relative
    closedness of that set in K(X)* stated in Federer 2.5.19, p. 113. *)
Theorem daniell_support_relatively_closed (S : set X) (A : (X -> R) -> R) :
  closed S -> is_daniell_integral K A ->
  closure [set B : daniell_weak_space K | is_daniell_integral K B /\
    compact_support_daniell_support B `<=` S] A ->
  compact_support_daniell_support A `<=` S.
Proof.
move=> hS hA hcl x hx.
apply: contrapT=> hxS; apply: hx.
exists (~` S); last exact: hxS.
split; first by rewrite openC.
move=> g hg hgS.
have hZ : closed [set B : daniell_weak_space K | B g = 0].
  have -> : [set B : daniell_weak_space K | B g = 0]
    = (fun B : daniell_weak_space K => B g) @^-1` [set t : R | t = 0] by [].
  apply: preimage_closed; last exact: closed_eq.
  by move=> B _; exact: daniell_weak_evaluation_continuous hg B.
have hDZ : [set B : daniell_weak_space K | is_daniell_integral K B /\
    compact_support_daniell_support B `<=` S]
  `<=` [set B : daniell_weak_space K | B g = 0].
  move=> B [hB hBS]; apply: daniell_support_vanishing hB hg _.
  apply: (subset_trans hgS); exact: subsetC hBS.
have := closureS hDZ hcl.
by rewrite -((closure_id _).1 hZ).
Qed.

End Embedding.
