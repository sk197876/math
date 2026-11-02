(** Federer (1969), 3.2.20, pp. 256–257: the multiplicity
    N(f,z) counts fibres of the original function on W. Keep its
    exact partial graph and use the existing sealed counting measure
    from 2.10.9, p. 175. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionSourceRestriction PartialFunctionExtensionUP
  CountingMeasure MeasureUP MeasureBasic MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_mapping_fibre]: the actual inverse image
    of z in N(f,z), Federer 3.2.20, p. 256, following
    2.10.9, p. 175. No extension values outside the original
    domain contribute to this fibre. *)
Definition partial_mapping_fibre (X Y : Type) (f : partial_function X Y) y : set X :=
  [set x | partial_function_graph f x y].

(** Source for [partial_mapping_multiplicity]: N(f,z) in Federer
    3.2.20, p. 256, evaluated through the abstract counting
    measure of 2.10.9, p. 175. Infinite and uncountable fibres
    are retained by the same sealed counting specification. *)
Definition partial_mapping_multiplicity (R : realType) (X : choiceType) (Y : Type)
    (f : partial_function X Y) y : \bar R :=
  counting_measure (R:=R) (partial_mapping_fibre f y).

(** Source for [partial_mapping_multiplicity_nonnegative]: nonnegative
    fibre count in the area integrand of Federer 3.2.20,
    p. 256, from the counting-measure laws of 2.1.2, p. 54. *)
Lemma partial_mapping_multiplicity_nonnegative (R : realType) (X : choiceType) (Y : Type)
    (f : partial_function X Y) y : 0<=@partial_mapping_multiplicity R X Y f y.
Proof. exact: (@measure_nonnegative R X (@counting_measure R X)
  (counting_measure_is_measure R X) (partial_mapping_fibre f y)). Qed.

(** Source for [partial_mapping_fibre_total_extension]: graph-preserving
    extensions do not change N(f,z), supporting the passage to F
    in Federer 3.2.20, p. 257. The total extension remains
    restricted to the exact original domain. *)
Lemma partial_mapping_fibre_total_extension (X Y : Type)
    (f : partial_function X Y) (F : X -> Y) y :
  is_partial_function_total_extension f F ->
  partial_mapping_fibre f y=mapping_fibre F (partial_function_domain f) y.
Proof.
move=> hExt; apply/seteqP; split.
- move=> x hx; split; first by exists y.
  exact: hExt x y hx.
- move=> x [[z hz] hFy].
  have hzy : z=y := eq_trans (esym (hExt x z hz)) hFy.
  by rewrite -hzy.
Qed.

(** Source for [partial_mapping_multiplicity_total_extension]: exact
    identification of original and extended-map multiplicities in Federer
    3.2.20, p. 257. This uses equality of actual fibres,
    independently of their cardinality or measurability. *)
Lemma partial_mapping_multiplicity_total_extension (R : realType) (X : choiceType) (Y : Type)
    (f : partial_function X Y) (F : X -> Y) y :
  is_partial_function_total_extension f F ->
  @partial_mapping_multiplicity R X Y f y=@mapping_multiplicity R X Y F (partial_function_domain f) y.
Proof. by move=> hExt; rewrite /partial_mapping_multiplicity /mapping_multiplicity (@partial_mapping_fibre_total_extension X Y f F y hExt). Qed.

(** Source for [partial_mapping_fibre_source_restrict]: restriction to
    the disjoint compact image pieces in Federer 3.2.20, p. 257.
    A fibre of the restricted partial function is precisely the old
    fibre intersected with the selected source set. *)
Lemma partial_mapping_fibre_source_restrict (X Y : Type) (A : set X)
    (f : partial_function X Y) y :
  partial_mapping_fibre (partial_function_source_restrict A f) y=A `&` partial_mapping_fibre f y.
Proof. reflexivity. Qed.
