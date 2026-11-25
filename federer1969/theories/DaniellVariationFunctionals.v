(** Federer (1969), 2.5.5, p. 97: both variations satisfy the monotone
    Daniell hypotheses on L+. The definitions use the sealed supremum
    implementation; the laws are proved from the abstract specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellIntegralNegation
  MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariation
  DaniellVariationBounds DaniellVariationAddition DaniellVariationScaling DaniellVariationIncreasing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [positive_variation_monotone_daniell]: the four properties of
    mu+ established in Federer 2.5.5, p. 97, before applying 2.5.2 *)
Theorem positive_variation_monotone_daniell (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_positive_variation L A P ->
  is_monotone_daniell_integral (positive_function_lattice L) P.
Proof.
move=> hL hA hP; constructor.
- exact: (@daniell_positive_variation_add R X L A P hL hA hP).
- exact: (@daniell_positive_variation_scale R X L A P hL hA hP).
- exact: (@daniell_positive_variation_monotone R X L A P hP).
- exact: (@daniell_positive_variation_increases R X L A P hL hA hP).
Qed.

(** Source for [negative_variation_monotone_daniell]: the same conclusion
    for mu-=(-mu)+ in Federer 2.5.5, p. 97 *)
Theorem negative_variation_monotone_daniell (R : realType) (X : Type)
    (L : set (X -> R)) (A Q : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_negative_variation L A Q ->
  is_monotone_daniell_integral (positive_function_lattice L) Q.
Proof.
move=> hL hA hQ.
exact: (@positive_variation_monotone_daniell R X L (fun f => - A f) Q hL
  (@daniell_integral_negate R X L A hL hA) hQ).
Qed.

(** Source for [daniell_negative_variation]: direct mu- of Federer 2.5.5, p.
    96, using the equality mu-=(-mu)+ proved on p. 97 *)
Definition daniell_negative_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :=
  @daniell_positive_variation R X L (fun f => - A f) hL
    (@daniell_integral_negate R X L A hL hA).

(** Source for [daniell_negative_variation_specification]: abstract
    negative-infimum law for the sealed mu- in Federer 2.5.5, p. 96, in the
    dual supremum form used by the proof on p. 97 *)
Lemma daniell_negative_variation_specification (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :
  is_daniell_negative_variation L A (@daniell_negative_variation R X L A hL hA).
Proof. exact: daniell_positive_variation_specification. Qed.
