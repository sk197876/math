(** Supporting dimension alternatives for the sharp correction to
    Federer 1.4.5, p. 20. State zero, line and independent-pair properties
    intrinsically, using the existing basis and independence predicates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates FiniteIndependence
  FiniteBasisCriterion InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [vector_space_is_zero]: supporting zero-space predicate
    for the corrected exceptions in Federer 1.4.5, p. 20. *)
Definition vector_space_is_zero (K : fieldType) (V : lmodType K) :=
  forall x : V, x=0.

(** Source for [vector_space_is_line]: supporting dimension-one predicate
    for Federer 1.4.5, p. 20. A singleton basis expresses a line without
    choosing coordinates or imposing finite dimension on other spaces. *)
Definition vector_space_is_line (K : fieldType) (V : lmodType K) :=
  exists e : 'I_1 -> V, is_basis e.

(** Source for [vector_space_has_pair]: supporting dimension-at-least-two
    predicate for Federer 1.4.5, p. 20. It applies in finite and infinite
    dimension and supplies precisely the existing commutator witnesses. *)
Definition vector_space_has_pair (K : fieldType) (V : lmodType K) :=
  exists e : 'I_2 -> V, finite_independent e.

(** Source for [vector_space_not_zero_has_nonzero]: supporting boundary
    connection for Federer 1.4.5, p. 20. A source which is not zero
    supplies a nonzero vector for the normalized-functional argument. *)
Lemma vector_space_not_zero_has_nonzero (K : fieldType) (V : lmodType K) :
    ~ vector_space_is_zero V -> exists v : V, v != 0.
Proof.
move=> hn.
apply: contrapT => hno; apply: hn => v.
apply/eqP; apply/negPn/negP => hv; apply: hno; by exists v.
Qed.

(** Source for [vector_space_small_or_pair]: supporting complete
    dimension alternative for Federer 1.4.5, p. 20. A nonzero vector
    either spans the whole space, giving a singleton basis, or an element
    outside its span extends it to an independent pair. Reuse the
    independent-family extension and finite-basis criterion. *)
Theorem vector_space_small_or_pair (K : fieldType) (V : lmodType K) :
    vector_space_is_zero V \/ vector_space_is_line V \/
      vector_space_has_pair V.
Proof.
have [hz|hz] := pselect (vector_space_is_zero V); first by left.
have [v hv] := vector_space_not_zero_has_nonzero hz.
have hi : finite_independent (fun _ : 'I_1 => v).
  move=> c hc i; rewrite big_ord1 in hc.
  have hc0 : c ord0=0.
    move/eqP: hc; by rewrite scaler_eq0 (negbTE hv) orbF => /eqP.
  by rewrite (ord1 i).
have [hs|hs] := pselect (forall w : V, exists c : K, w=c*:v).
- right; left; exists (fun _ : 'I_1 => v).
  apply: finite_basis_criterion hi _ => w.
  have [c hc] := hs w; exists (fun _ => c); by rewrite big_ord1.
- have [w hw] : exists w : V, ~ exists c : K, w=c*:v.
    apply: contrapT => hno; apply: hs => w.
    apply: contrapT => hw; apply: hno; by exists w.
  have hout (c : 'I_1 -> K) : w != \sum_i c i *: v.
    apply/eqP => hc; apply: hw; exists (c ord0).
    by rewrite big_ord1 in hc.
  right; right; exists (ordinal_snoc (fun _ : 'I_1 => v) w).
  exact: finite_independent_snoc hi hout.
Qed.

(** Source for [vector_space_without_pair_small]: supporting exhaustive
    small-space connection for Federer 1.4.5, p. 20. Absence of an
    independent pair leaves exactly the zero-space or line alternatives. *)
Lemma vector_space_without_pair_small (K : fieldType) (V : lmodType K) :
    ~ vector_space_has_pair V ->
    vector_space_is_zero V \/ vector_space_is_line V.
Proof.
move=> hn; case: (@vector_space_small_or_pair K V) => [hz|[hl|hp]].
- by left.
- by right.
- by exfalso; apply: hn.
Qed.
