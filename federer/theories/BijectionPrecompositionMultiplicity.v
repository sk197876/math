(** Supporting Federer (1969), 2.10.46, p. 204: changing the source
    coordinates of the cylinder does not change multiplicity. This is the
    elementary fibre bijection used in Freilich (1950), Theorem 4.5, Parts
    1–4, pp. 242–247. Infinite fibres are retained by the numerical-sum
    definition of counting measure, 2.1.2, p. 54. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MappingMultiplicity CountingInjectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bijective_precomposition_multiplicity]: supporting
    source-coordinate invariance in 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 1–4,
    pp. 242–247. Explicit inverse laws suffice; neither
    measurability nor finiteness of the fibres is required. *)
Lemma bijective_precomposition_multiplicity (R : realType) (X Y Z : choiceType)
    (u : X -> Y) (v : Y -> X) (f : Y -> Z) (A : set X) z :
  cancel u v -> cancel v u ->
  @mapping_multiplicity R X Z (fun x=>f (u x)) A z=
    @mapping_multiplicity R Y Z f (u @` A) z.
Proof.
move=> huv hvu; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@counting_measure_injection_bound R X Y _ _ u).
  + move=> x [hx he]; split=> //; by exists x.
  + move=> x y _ _ he; have hh := congr1 v he; by rewrite !huv in hh.
- apply: (@counting_measure_injection_bound R Y X _ _ v).
  + move=> y [[x hx <-] he]; by rewrite huv.
  + move=> x y _ _ he; have hh := congr1 u he; by rewrite !hvu in hh.
Qed.
