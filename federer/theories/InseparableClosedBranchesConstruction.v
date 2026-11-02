(** Federer (1969), 2.2.10(1), p. 67: private inductive construction of
    inseparable closed branches. We refine only the selected closed sets,
    using the small covers of 2.2.8; unused siblings need not be stored. The
    public interface exposes branch laws only. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import BorelSeparation BorelSeparationRefinement
  ClosedCoverTreeUP SeparableClosedCover InseparableClosedBranchesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_image_small_inseparable_refinement]: supporting
    child-pair choice for Federer 2.2.10(1), p. 67. Cover each nonempty
    closed parent by countably many small closed sets. Some pair of child
    images remains inseparable, by contraposition of the corrected union
    lemma. erratum p. 1, book p. 67 line 2. *)
Lemma closed_image_small_inseparable_refinement (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (H C D : set T) (e : R) :
  countable H -> dense H -> closed C -> closed D -> 0 < e ->
  ~ borel_separated (f @` C) (f @` D) ->
  exists P Q : set T,
    closed P /\ closed Q /\ P `<=` C /\ Q `<=` D /\
    (forall x y, P x -> P y -> mdist x y <= e) /\
    (forall x y, Q x -> Q y -> mdist x y <= e) /\
    ~ borel_separated (f @` P) (f @` Q).
Proof.
move=> hc hd hC hD he hn.
have [hnC hnD] := non_borel_separated_nonempty hn.
have hCne : C !=set0 by have [y [x hx _]] := hnC; exists x.
have hDne : D !=set0 by have [y [x hx _]] := hnD; exists x.
have [P [hP hCP]] := @separable_closed_small_cover R T H C e hc hd hC hCne he.
have [Q [hQ hDQ]] := @separable_closed_small_cover R T H D e hc hd hD hDne he.
have hpi : f @` C = \bigcup_i (f @` P i).
  rewrite hCP; apply/seteqP; split.
  - move=> y [x [i _ hx] <-]; exists i=> //; by exists x.
  - move=> y [i _ [x hx <-]]; exists x=> //; by exists i.
have hqi : f @` D = \bigcup_i (f @` Q i).
  rewrite hDQ; apply/seteqP; split.
  - move=> y [x [i _ hx] <-]; exists i=> //; by exists x.
  - move=> y [i _ [x hx <-]]; exists x=> //; by exists i.
rewrite hpi hqi in hn.
have [i [j hij]] := non_borel_separated_sequence_refinement hn.
exists (P i),(Q j); split; first exact: (hP i).1.
split; first exact: (hQ j).1.
split; first exact: (hP i).2.2.1.
split; first exact: (hQ j).2.2.1.
split; first exact: (hP i).2.2.2.
split=> //; exact: (hQ j).2.2.2.
Qed.
