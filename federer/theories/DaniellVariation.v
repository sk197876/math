(** Public positive variation for Federer (1969), 2.5.5, p. 96 Downstream
    proofs use the supremum laws, never the construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [daniell_positive_variation]: direct mu+ of Federer 2.5.5, p.
    96 *)
Definition daniell_positive_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :=
  @DaniellVariation.value R X L A hL hA.

(** Source for [daniell_positive_variation_specification]: exact supremum
    formula of Federer 2.5.5, p. 96 *)
Lemma daniell_positive_variation_specification (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :
  is_daniell_positive_variation L A (@daniell_positive_variation R X L A hL hA).
Proof. exact: (@DaniellVariation.laws R X L A hL hA). Qed.
