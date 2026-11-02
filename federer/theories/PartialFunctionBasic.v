(** Federer (1969), 2.3.1, p. 72: supporting laws of the equality locus for
    partially defined functions. All proofs use only the single-valued graph
    specification. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_agreement_self]: supporting domain
    qualification for almost equality in Federer 2.3.1, p. 72 *)
Lemma partial_function_agreement_self (X Y : Type) (f : partial_function X Y) :
  partial_function_agreement f f = partial_function_domain f.
Proof.
apply/seteqP; split=> x; first by move=> [y [hy _]]; exists y.
by move=> [y hy]; exists y; split.
Qed.

(** Source for [partial_function_agreement_sym]: supporting symmetry
    of the equality locus in Federer 2.3.1, p. 72. *)
Lemma partial_function_agreement_sym (X Y : Type) (f g : partial_function X Y) :
  partial_function_agreement f g = partial_function_agreement g f.
Proof. apply/seteqP; split=> x [y [hf hg]]; exists y; by split. Qed.

(** Source for [partial_function_agreement_trans]: supporting
    transitivity at common domain points in Federer 2.3.1, p. 72.
    Single-valuedness of the intermediate function identifies its values. *)
Lemma partial_function_agreement_trans (X Y : Type) (f g h : partial_function X Y) :
  partial_function_agreement f g `&` partial_function_agreement g h
    `<=` partial_function_agreement f h.
Proof.
move=> x [[y [hf hg]] [z [hg' hh]]].
have he : y = z := partial_function_single_valued hg hg'.
rewrite -he in hh.
by exists y; split.
Qed.

(** Source for [partial_function_agreement_domain_left]: supporting
    common-domain condition in Federer 2.3.1, p. 72. *)
Lemma partial_function_agreement_domain_left (X Y : Type)
    (f g : partial_function X Y) :
  partial_function_agreement f g `<=` partial_function_domain f.
Proof. by move=> x [y [hy _]]; exists y. Qed.

(** Source for [partial_function_preimage_whole]: the domain is
    the inverse image of the whole target in Federer 2.3.2, p. 73. *)
Lemma partial_function_preimage_whole (X Y : Type) (f : partial_function X Y) :
  partial_function_preimage f setT = partial_function_domain f.
Proof.
apply/seteqP; split=> x; first by move=> [y [hy _]]; exists y.
by move=> [y hy]; exists y; split.
Qed.

(** Source for [partial_function_total]: supporting inclusion of
    ordinary total maps in the function convention of Federer
    2.3.1, p. 72. Its graph is specified by its given values. *)
Definition partial_function_total (X Y : Type) (f : X -> Y) : partial_function X Y.
Proof.
refine (@Build_partial_function X Y (fun x y => f x = y) _).
by move=> x y z <- <-.
Defined.

(** Source for [partial_function_empty]: supporting empty-domain
    function in Federer 2.3.1, p. 72, and 2.3.2, p. 73.
    This exists even if the target is empty. *)
Definition partial_function_empty (X Y : Type) : partial_function X Y.
Proof. refine (@Build_partial_function X Y (fun _ _ => False) _); by move=> x y z []. Defined.

(** Source for [partial_function_total_domain]: supporting total
    domain case of Federer 2.3.1, p. 72. *)
Lemma partial_function_total_domain (X Y : Type) (f : X -> Y) :
  partial_function_domain (partial_function_total f) = setT.
Proof. apply/seteqP; split=> x _=> //; by exists (f x). Qed.

(** Source for [partial_function_empty_domain]: supporting
    empty-domain boundary of the convention in Federer 2.3.1, p. 72. *)
Lemma partial_function_empty_domain (X Y : Type) :
  partial_function_domain (@partial_function_empty X Y) = set0.
Proof. apply/seteqP; split=> x; first by move=> [y []]. by move=> []. Qed.

(** Source for [partial_function_total_agreement]: direct
    equality locus from Federer 2.3.1, p. 72, for total maps. *)
Lemma partial_function_total_agreement (X Y : Type) (f g : X -> Y) :
  partial_function_agreement (partial_function_total f) (partial_function_total g)
    = [set x | f x = g x].
Proof.
apply/seteqP; split=> x.
- move=> [y [hf hg]]; exact (eq_trans hf (esym hg)).
- move=> he; exists (f x); split; first by [].
  exact (esym he).
Qed.
