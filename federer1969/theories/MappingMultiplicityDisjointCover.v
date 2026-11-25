(** Federer (1969), 3.2.20, p. 257: multiplicities
    sum over the disjoint compact images, outside the image of the
    uncovered null source remainder. Counting measure gives the
    identity even when a fibre is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum CountingMeasure MappingMultiplicity MeasureUP
  MeasureCountableAdditivity MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_disjoint_cover]: supporting exact
    fibre decomposition in the last step of Federer 3.2.20,
    p. 257, by 2.1.3(3), p. 55, for counting measure.
    The fibre need not be finite or countable. *)
Lemma mapping_multiplicity_disjoint_cover (R : realType) (X Y : choiceType)
    (F : X -> Y) (W : set X) (E : nat -> set X) z :
  (forall i,E i `<=` W) ->
  (forall i j,i!=j -> forall x,E i x -> E j x -> False) ->
  ~ (F @` (W `\` (\bigcup_i E i))) z ->
  @mapping_multiplicity R X Y F W z=nonnegative_sum setT
    (fun i=>@mapping_multiplicity R X Y F (E i) z).
Proof.
move=> hSub hDisj hOutside.
have hFibre : mapping_fibre F W z=\bigcup_i mapping_fibre F (E i) z.
  apply/seteqP; split=> x.
  - move=> [hx hF].
    have hIn : (\bigcup_i E i) x.
      apply: contrapT=> hn; apply: hOutside; exists x; last exact hF; by split.
    have [i hi hEi] := hIn; exists i; first exact hi; by split.
  - move=> [i hi [hEi hF]]; split; [exact: hSub i x hEi|exact hF].
rewrite /mapping_multiplicity hFibre.
apply: (@measure_sequence_disjoint_additivity R X (@counting_measure R X)
  (counting_measure_is_measure R X) (fun i=>mapping_fibre F (E i) z)).
- move=> i; exact: counting_measure_measurable.
- move=> i j hij x [hx hF] [hy hG]; exact: (hDisj i j hij x hx hy).
Qed.

(** Source for [mapping_multiplicity_almost_disjoint_cover]: supporting
    almost-everywhere count identity in Federer 3.2.20,
    p. 257. The image of the omitted remainder is proved
    null in the geometric application by 2.10.11, p. 176. *)
Lemma mapping_multiplicity_almost_disjoint_cover (R : realType) (X Y : choiceType)
    (nu : set Y -> \bar R) (hn : is_measure nu)
    (F : X -> Y) (W : set X) (E : nat -> set X) :
  (forall i,E i `<=` W) ->
  (forall i j,i!=j -> forall x,E i x -> E j x -> False) ->
  nu (F @` (W `\` (\bigcup_i E i)))=0 ->
  measure_almost_everywhere nu [set z|
    nonnegative_sum setT (fun i=>@mapping_multiplicity R X Y F (E i) z)=
      @mapping_multiplicity R X Y F W z].
Proof.
move=> hSub hDisj hNull.
have hOff : measure_almost_everywhere nu (~` (F @` (W `\` (\bigcup_i E i)))).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hOff)=> z hz.
exact: (esym (@mapping_multiplicity_disjoint_cover R X Y F W E z hSub hDisj hz)).
Qed.
