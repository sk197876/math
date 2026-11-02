(** Opaque coordinate-change witness for Federer (1969), 3.1.3(3),
    p. 213. Downstream proofs use the inverse and first-block laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanEpimorphismChartUP
  EuclideanEpimorphismChartConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type EuclideanEpimorphismChartSignature.
(** Source for [value]: the isomorphism beta used in Federer
    3.1.3(3), p. 213, represented before its standard block split. *)
Parameter value : forall (R : realType) n m
  (p : {linear R_n R n -> R_n R m}), (forall y, exists x, p x=y) ->
  {hmn : (m<=n)%N &
    ({linear R_n R n -> R_n R n} * {linear R_n R n -> R_n R n})%type}.
(** Source for [laws]: inverse identities and the prescribed first
    block of beta, Federer 3.1.3(3), p. 213. *)
Parameter laws : forall (R : realType) n m
  (p : {linear R_n R n -> R_n R m}) (hp : forall y, exists x, p x=y),
  let w := @value R n m p hp in
  is_euclidean_epimorphism_chart p (projT1 w) (projT2 w).1 (projT2 w).2.
End EuclideanEpimorphismChartSignature.

Module EuclideanEpimorphismChart : EuclideanEpimorphismChartSignature.
(** Source for [value]: selection from the proved existence of beta
    in Federer 3.1.3(3), p. 213. The private construction is sealed. *)
Definition value (R : realType) n m (p : {linear R_n R n -> R_n R m})
    (hp : forall y, exists x, p x=y) :=
  projT1 (cid (euclidean_epimorphism_chart_exists hp)).
(** Source for [laws]: the selected coordinate change satisfies
    its abstract specification, Federer 3.1.3(3), p. 213. *)
Lemma laws (R : realType) n m (p : {linear R_n R n -> R_n R m})
    (hp : forall y, exists x, p x=y) :
  let w := @value R n m p hp in
  is_euclidean_epimorphism_chart p (projT1 w) (projT2 w).1 (projT2 w).2.
Proof. exact: projT2 (cid (euclidean_epimorphism_chart_exists hp)). Qed.
End EuclideanEpimorphismChart.
