(** Federer (1969), 2.3.2, p. 73, opening Borel-family argument:
    inverse-image algebra for functions with partial domains. Complements
    are taken inside the domain, not inside the whole source. These are
    supporting set-theoretic laws, not imported measure-theory results. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_preimage_empty]: supporting
    empty-set law for Federer 2.3.2, p. 73, Borel-family paragraph. *)
Lemma partial_function_preimage_empty (X Y : Type) (f : partial_function X Y) :
  partial_function_preimage f set0 = set0.
Proof. apply/seteqP; split=> x; first by move=> [y [_ []]]. by move=> []. Qed.

(** Source for [partial_function_preimage_mono]: supporting
    monotonicity of inverse images in Federer 2.3.2, p. 73. *)
Lemma partial_function_preimage_mono (X Y : Type) (f : partial_function X Y)
    (A B : set Y) : A `<=` B -> partial_function_preimage f A `<=` partial_function_preimage f B.
Proof. move=> h x [y [hf hy]]; exists y; split=> //; exact: h hy. Qed.

(** Source for [partial_function_preimage_complement]: supporting
    complement law in Federer 2.3.2, p. 73, opening argument.
    Its right side uses the actual domain of the partial map. *)
Lemma partial_function_preimage_complement (X Y : Type) (f : partial_function X Y)
    (A : set Y) : partial_function_preimage f (~` A) =
      partial_function_domain f `\` partial_function_preimage f A.
Proof.
apply/seteqP; split=> x.
- move=> [y [hf hn]]; split; first by exists y.
  move=> [z [hz ha]]; apply: hn.
  have he : y = z := partial_function_single_valued hf hz.
  by rewrite he.
- move=> [[y hf] hn]; exists y; split=> // ha; apply: hn; by exists y.
Qed.

(** Source for [partial_function_preimage_union]: supporting
    indexed union law in Federer 2.3.2, p. 73. It holds for
    arbitrary index families; only the measurable-set consequence
    needs countability. Empty families are included. *)
Lemma partial_function_preimage_union (X Y J : Type) (f : partial_function X Y)
    (D : set J) (A : J -> set Y) :
  partial_function_preimage f (\bigcup_(j in D) A j) =
  \bigcup_(j in D) partial_function_preimage f (A j).
Proof.
apply/seteqP; split=> x.
- move=> [y [hf [j hj hy]]]; exists j=> //; by exists y.
- move=> [j hj [y [hf hy]]]; exists y; split=> //; by exists j.
Qed.

(** Source for [partial_function_preimage_intersection]: supporting
    intersection law in Federer 2.3.2, p. 73. The explicit domain
    factor also makes the formula correct for an empty index family. *)
Lemma partial_function_preimage_intersection (X Y J : Type) (f : partial_function X Y)
    (D : set J) (A : J -> set Y) :
  partial_function_preimage f (\bigcap_(j in D) A j) =
  partial_function_domain f `&` (\bigcap_(j in D) partial_function_preimage f (A j)).
Proof.
apply/seteqP; split=> x.
- move=> [y [hf ha]]; split; first by exists y.
  move=> j hj; exists y; split=> //; exact: ha j hj.
- move=> [[y hf] ha]; exists y; split=> // j hj.
  have [z [hz hza]] := ha j hj.
  have he : y = z := partial_function_single_valued hf hz.
  by rewrite he.
Qed.

(** Source for [partial_function_total_preimage]: supporting
    agreement with ordinary inverse images for the total extension
    in Federer 2.3.2, p. 73, second paragraph. *)
Lemma partial_function_total_preimage (X Y : Type) (h : X -> Y) (A : set Y) :
  partial_function_preimage (partial_function_total h) A = h @^-1` A.
Proof.
apply/seteqP; split=> x.
- by move=> [y [<- ha]].
- by move=> ha; exists (h x).
Qed.
