(** Federer (1969), 3.3.19, p. 303: exact
    membership, monotonicity and finite union laws for the
    original finite cell-hit indices. No measurability
    of the original test sets is required. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Section Indices.
Variables I X:choiceType.
Variable F:{fset I}.
Variable S:I->set X.

(** Source for [finite_cell_hit_indices_membership]: exact
    original index and actual meeting-point description
    of psi_n's hit family, 3.3.19, p. 303. *)
Lemma finite_cell_hit_indices_membership (T:set X) (i:I):
  i \in finite_cell_hit_indices F S T <->i \in F /\exists x,S i x /\T x.
Proof.
rewrite /finite_cell_hit_indices in_fset /= !inE.
split=>[/andP[hi /asboolP hHit]|[hi hHit]];first by split.
apply/andP;split=>//;exact/asboolP.
Qed.

(** Source for [finite_cell_hit_indices_monotone]: enlarging
    the original test set enlarges its actual hit family,
    supporting 3.3.19, p. 303. *)
Lemma finite_cell_hit_indices_monotone (T U:set X):T `<=` U ->
  (finite_cell_hit_indices F S T `<=` finite_cell_hit_indices F S U)%fset.
Proof.
move=>hTU;apply/fsubsetP=>i /finite_cell_hit_indices_membership[hi [x [hxS hxT]]].
apply/finite_cell_hit_indices_membership;split=>//;exists x;split=>//;exact:hTU x hxT.
Qed.

(** Source for [finite_cell_hit_indices_subset]: the
    actual original hit family is a subfamily of
    the original finite cells, 3.3.19, p. 303. *)
Lemma finite_cell_hit_indices_subset (T:set X):
  (finite_cell_hit_indices F S T `<=` F)%fset.
Proof.
apply/fsubsetP=>i /finite_cell_hit_indices_membership[hi _];exact hi.
Qed.
End Indices.
