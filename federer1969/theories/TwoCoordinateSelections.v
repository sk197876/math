(** Federer (1969), 1.7.4, p. 31, and 3.2.27,
    p. 262: in the plane there are exactly two
    singleton coordinate projections. These finite-index
    laws support the actual two-sheet counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import ExteriorIndices SingleCoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [singleton_selection_from_coordinate]: the
    singleton-coordinate case of Lambda(n,m) in 1.7.4,
    p. 31, used in 3.2.27, p. 262. An
    increasing one-tuple is determined by its sole entry. *)
Lemma singleton_selection_from_coordinate n (lambda:Lambda n 1):
  lambda=single_coordinate_selection (tnth (val lambda) ord0).
Proof.
apply:val_inj; apply:eq_from_tnth=>i.
by rewrite (ord1 i) /single_coordinate_selection /= tnth0.
Qed.

(** Source for [two_coordinate_selections]: the two
    coordinate projections in the plane, supporting the
    local counterexample to 3.2.27, pp. 262–263. *)
Lemma two_coordinate_selections (lambda:Lambda 2 1):
  lambda=single_coordinate_selection (ord0:'I_2) \/
  lambda=single_coordinate_selection (ord_max:'I_2).
Proof.
rewrite (singleton_selection_from_coordinate lambda).
case:(tnth (val lambda) ord0)=>[[|[|i]] hi].
- left; congr (single_coordinate_selection _); apply:val_inj; reflexivity.
- right; congr (single_coordinate_selection _); apply:val_inj; reflexivity.
- exfalso; by move:hi; rewrite !ltnS ltn0.
Qed.

(** Source for [two_coordinate_selections_distinct]: the
    two Lambda(2,1) indices in the local test of
    3.2.27, pp. 262–263, are distinct actual
    coordinate selections. *)
Lemma two_coordinate_selections_distinct:
  single_coordinate_selection (ord0:'I_2)!=single_coordinate_selection (ord_max:'I_2).
Proof.
apply/eqP=>he.
have h:=congr1 (fun lambda:Lambda 2 1=>val (tnth (val lambda) ord0)) he.
by rewrite /single_coordinate_selection /= in h.
Qed.
