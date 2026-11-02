(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Elements of V_1 × … × V_m are dependent finite functions on 'I_m.
    Replacing one component is the basic operation of multilinearity. *)
Section FamilyUpdate.
Variable m : nat.
Variable V : 'I_m -> Type.

(** Source for [family_with]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Definition or construction used to
    formalise this passage. *)
Definition family_with (x : {dffun forall i, V i}) (i : 'I_m) (v : V i) :
    {dffun forall i, V i} :=
  [ffun j => dfwith x v j].

(** Source for [family_with_in]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_with_in x i (v : V i) : family_with x v i = v.
Proof. by rewrite ffunE dfwith_in. Qed.

(** Source for [family_with_out]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_with_out x i (v : V i) j : i != j -> family_with x v j = x j.
Proof. by move=> h; rewrite ffunE dfwith_out. Qed.

(** Source for [family_with_id]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_with_id x i : family_with x (x i) = x.
Proof.
apply/ffunP=> j; case: (eqVneq i j) => [<-|h].
  by rewrite family_with_in.
by rewrite family_with_out.
Qed.

(** Source for [family_with_with]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_with_with x i (v w : V i) :
  family_with (family_with x v) w = family_with x w.
Proof.
apply/ffunP=> j; case: (eqVneq i j) => [<-|h].
  by rewrite !family_with_in.
by rewrite !family_with_out.
Qed.
End FamilyUpdate.

Section FamilyMap.
Variable m : nat.
Variables V W : 'I_m -> Type.
Variable f : forall i, V i -> W i.

(** The componentwise map x ↦ (f_1(x_1), …, f_m(x_m)). *)
(** Source for [family_map]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Definition or construction used to
    formalise this passage. *)
Definition family_map (x : {dffun forall i, V i}) : {dffun forall i, W i} :=
  [ffun i => f (x i)].

(** Source for [family_mapE]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_mapE x i : family_map x i = f (x i).
Proof. by rewrite ffunE. Qed.

(** Source for [family_map_with]: Federer (1969), 1.1.1, p. 8, opening
    definition. In words: An n-linear function is linear in each argument
    when all other arguments are fixed. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma family_map_with x i (v : V i) :
  family_map (family_with x v) = family_with (family_map x) (f v).
Proof.
apply/ffunP=> j; rewrite family_mapE; case: (eqVneq i j) => [<-|h].
  by rewrite !family_with_in.
by rewrite !family_with_out // family_mapE.
Qed.
End FamilyMap.
