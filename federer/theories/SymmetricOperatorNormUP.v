(** Federer (1969), 1.10.5, p. 47, the displayed supremum defining the norm
    of a symmetric multilinear form. The specification permits positive
    infinity and does not assume finite-dimensional V or boundedness. Input
    seminorms suffice for this definition; subsequent estimates state
    explicitly when positive definiteness or finiteness is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Specification.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Variable NW : W -> R.
Variable m : nat.

(** Source for [symmetric_form_unit_tuple]: Federer 1.10.5,
    p. 47, the constraint in the form-norm supremum: every input
    vector has norm at most one. For degree zero the constraint is empty. *)
Definition symmetric_form_unit_tuple (t : m.-tuple V) : Prop :=
  forall i, NV (tnth t i) <= 1.

(** Source for [symmetric_form_unit_values]: Federer 1.10.5,
    p. 47, the set whose supremum defines the form norm.
    Its elements are the output norms of evaluations on unit-ball tuples. *)
Definition symmetric_form_unit_values (f : S_m V W m) : set R :=
  fun r => exists t, symmetric_form_unit_tuple t /\ r = NW (f t).

(** Source for [is_symmetric_operator_norm]: Federer 1.10.5,
    p. 47, abstract definition of the form norm by its least-upper-bound
    laws. A value of positive infinity represents an unbounded form. *)
Definition is_symmetric_operator_norm (f : S_m V W m) (c : \bar R) : Prop :=
  is_extended_supremum (symmetric_form_unit_values f) c.

(** Source for [symmetric_form_unit_values_nonempty]: Federer 1.10.5,
    p. 47, supporting nonemptiness for existence of the supremum.
    The zero tuple belongs to the unit ball, including in degree zero. *)
Lemma symmetric_form_unit_values_nonempty (hN : is_real_seminorm NV)
    (f : S_m V W m) : symmetric_form_unit_values f !=set0.
Proof.
exists (NW (f [tuple (0:V) | i < m])); exists [tuple (0:V) | i < m]; split=> //.
move=> i; by rewrite tnth_mktuple (real_seminorm_zero hN) ler01.
Qed.

(** Source for [symmetric_operator_norm_unique]: Federer 1.10.5,
    p. 47, supporting uniqueness of the specified supremum,
    including the unbounded case. *)
Lemma symmetric_operator_norm_unique (f : S_m V W m) c d :
  is_symmetric_operator_norm f c -> is_symmetric_operator_norm f d -> c=d.
Proof. exact: extended_supremum_unique. Qed.

(** Source for [symmetric_operator_norm_unit_bound]: Federer 1.10.5,
    p. 47, the defining supremum bounds every unit-tuple value. *)
Lemma symmetric_operator_norm_unit_bound (f : S_m V W m) c :
  is_symmetric_operator_norm f c -> forall t, symmetric_form_unit_tuple t ->
    ((NW (f t))%:E <= c)%E.
Proof.
move=> hc t ht; apply: (@extended_supremum_upper R _ c hc).
by exists t.
Qed.

(** Source for [symmetric_operator_norm_le_finite]: Federer 1.10.5,
    p. 47, supporting characterization of finite upper bounds.
    The norm is at most L exactly when every unit-tuple value is at most L. *)
Lemma symmetric_operator_norm_le_finite (f : S_m V W m) c
    (hc : is_symmetric_operator_norm f c) L :
  (c <= L%:E)%E <-> forall t, symmetric_form_unit_tuple t -> NW (f t) <= L.
Proof.
split=> [h t ht|h].
- have hh := le_trans (@symmetric_operator_norm_unit_bound f c hc t ht) h.
  by move: hh; rewrite lee_fin.
- apply: (@extended_supremum_least R _ c hc); move=> r [t [ht ->]].
  rewrite lee_fin; exact: h ht.
Qed.

(** Source for [symmetric_operator_norm_nonnegative]: Federer 1.10.5,
    p. 47, nonnegativity of the form norm, including constant forms
    and maps from the zero-dimensional space. *)
Lemma symmetric_operator_norm_nonnegative (hV : is_real_seminorm NV)
    (hW : is_real_seminorm NW) (f : S_m V W m) c :
  is_symmetric_operator_norm f c -> (0 <= c)%E.
Proof.
move=> hc; apply: (@extended_supremum_nonnegative R _ c hc).
have [r [t [ht hr]]] := symmetric_form_unit_values_nonempty hV f.
exists (NW (f t)); split; last exact: real_seminorm_nonnegative hW (f t).
by exists t.
Qed.
End Specification.
