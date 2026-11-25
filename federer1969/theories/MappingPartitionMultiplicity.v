(** Federer (1969), 3.2.3, p. 243: multiplicity
    is the sum over the Borel partition, and on each
    univalent piece it is the characteristic function of
    the image. Fibres may have arbitrary cardinality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureCountableAdditivity
  CountingMeasure CountingInjectionBound MappingMultiplicity MappingMultiplicityLaws
  CountablyClosedFamilyUP BorelPartition CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_partition_multiplicity]: summing
    N(f restricted to B,y) over H in Federer 3.2.3,
    p. 243, by countable additivity of actual counting
    measure. The original fibres need not be countable. *)
Theorem mapping_partition_multiplicity (R:realType) (X:topologicalType) (Y:Type)
    (f:X->Y) (A:set X) (H:set (set X)):
  is_borel_partition A H -> forall y,@mapping_multiplicity R X Y f A y=
    nonnegative_sum H (fun B=>@mapping_multiplicity R X Y f B y).
Proof.
move=>hH y.
have hUnion:mapping_fibre f A y=\bigcup_(B in H) mapping_fibre f B y.
  rewrite -(borel_partition_union hH).
  apply/seteqP; split=>x.
  - by move=>[[B hB hx] hfx]; exists B=>//; split.
  - move=>[B hB [hx hfx]]; split; first by exists B.
    exact hfx.
rewrite /mapping_multiplicity hUnion.
apply:(@measure_countable_disjoint_additivity R X [the choiceType of set X]
  (@counting_measure R X) (counting_measure_is_measure R X) H (fun B=>mapping_fibre f B y)
  (borel_partition_countable hH)).
- move=>B hB; exact:counting_measure_measurable.
- move=>B C hB hC hNe x [hx _] [hx' _].
  have hn:B<>C by move=>he; by rewrite he eqxx in hNe.
  have hEmpty: B `&` C=set0:=borel_partition_disjoint hH hB hC hn.
  have hBoth:(B `&` C) x by split.
  by rewrite hEmpty in hBoth.
Qed.

(** Source for [injective_mapping_multiplicity_characteristic]:
    N(f restricted to B,y) is the characteristic function
    of f(B) for a univalent restriction, as used in
    Federer 3.2.3, p. 243. Empty pieces are included. *)
Lemma injective_mapping_multiplicity_characteristic (R:realType) (X:choiceType)
    (Y:Type) (f:X->Y) (B:set X) (s:Y->R):
  {in B &,injective f} -> is_characteristic_function (f @` B) s ->
  forall y,@mapping_multiplicity R X Y f B y=(s y)%:E.
Proof.
move=>hInj hs y; case:(pselect ((f @` B) y))=>hy.
- rewrite (characteristic_on_set hs hy).
  have [x hx hfx]:=hy.
  have hFiber:mapping_fibre f B y=[set x].
    apply/seteqP; split=>z.
    + move=>[hz hfz]; exact (hInj z x (mem_set hz) (mem_set hx) (eq_trans hfz (esym hfx))).
    + move=>->; by split.
  rewrite /mapping_multiplicity hFiber; exact:counting_measure_singleton_value.
- rewrite (characteristic_off_set hs hy).
  exact ((@mapping_multiplicity_zero_iff R X Y f B y).2 hy).
Qed.
