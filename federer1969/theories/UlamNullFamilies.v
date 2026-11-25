(** Federer (1969), 2.1.6, p. 58: equivalence between the point-null
    definition and the disjoint null-family definition of Ulam numbers.
    Families are indexed; repeated empty sets do not change their union.
    Source context: UlamCardinalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP UlamCardinalUP MeasureDisjointFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_null_family_property]: Federer 2.1.6,
    p. 58, second defining property, paraphrased: a disjoint family
    of null sets, with measurable subfamily unions and finite full
    union measure, has null union if its cardinality is at most D. *)
Definition ulam_null_family_property (R : realType) (K : choiceType) (C : set K) :=
  forall (I J : choiceType) (mu : set I -> \bar R) (D : set J) (F : J -> set I),
    is_measure mu -> D #<= C ->
    (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
    mu (\bigcup_(j in D) F j) < +oo ->
    (forall A, measure_measurable mu (measure_family_union D F A)) ->
    (forall j, D j -> mu (F j) = 0) -> mu (\bigcup_(j in D) F j) = 0.

(** Source for [ulam_set_null_families]: Federer 2.1.6,
    p. 58, proof of the second property from the first: place the
    induced union measure on the index space. Its singletons are
    null and all of its subsets are measurable. *)
Theorem ulam_set_null_families (R : realType) (K : choiceType) (C : set K) :
  is_ulam_set R C -> ulam_null_family_property R C.
Proof.
move=> hu I J mu D F hm hD hd hf ha hz.
pose nu := measure_family_image mu D F.
have hn : is_measure nu := measure_family_image_is_measure hm D F.
have hv : nu D = mu (\bigcup_(j in D) F j).
  by rewrite /nu /measure_family_image measure_family_union_full.
rewrite -hv; apply: (hu J nu D hn hD); first by rewrite hv.
- move=> A _; exact: (measure_family_image_all_measurable hd ha A).
- move=> j hj; by rewrite /nu /measure_family_image
    (measure_family_union_singleton F hj) (hz j hj).
Qed.

(** Source for [ulam_null_families_set]: Federer 2.1.6,
    p. 58, proof of the first property from the second: use the
    disjoint family of all singleton subsets of the measured set. *)
Theorem ulam_null_families_set (R : realType) (K : choiceType) (C : set K) :
  ulam_null_family_property R C -> is_ulam_set R C.
Proof.
move=> hu I mu X hm hX hf ha hz.
have he : (\bigcup_(x in X) [set x]) = X.
  apply/seteqP; split=> [y [x hx ->]|x hx] //; by exists x.
rewrite -he; apply: (hu I I mu X (fun x => [set x]) hm hX).
- move=> j k _ _ hn; apply/seteqP; split=> [x [hj hk]|x []].
  exfalso; apply: hn; by rewrite -hj hk.
- by rewrite he.
- move=> A; apply: ha=> x [j [hj _] ->]; exact hj.
- exact hz.
Qed.

(** Source for [ulam_set_null_families_iff]: Federer 2.1.6,
    p. 58: the two displayed properties are equivalent. The indexed
    version applies to the printed set-family by taking its members
    as indices and the inclusion map as the family. *)
Theorem ulam_set_null_families_iff (R : realType) (K : choiceType) (C : set K) :
  is_ulam_set R C <-> ulam_null_family_property R C.
Proof. split; [exact: ulam_set_null_families | exact: ulam_null_families_set]. Qed.
