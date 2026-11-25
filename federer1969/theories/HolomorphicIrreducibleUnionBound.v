(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 321: an
    irreducible variety germ contained in a finite union
    is contained in one original member. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric SetGermUP SetGermSealed SetGermLaws SetGermOrder
  SetGermBooleanOrder SetGermBoundary SetGermFiniteUnion HolomorphicVarietyGermUP HolomorphicVarietyGermBooleanClosure
  HolomorphicIrreducibleGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section UnionBound.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T a).
Local Notation V alpha:=(@is_holomorphic_variety_germ R X NX hNX a alpha).
Local Notation IR alpha:=(@is_union_irreducible_holomorphic_germ R X NX hNX a alpha).
Local Notation NI alpha:=(@is_nonempty_irreducible_holomorphic_germ R X NX hNX a alpha).
Local Notation join:=(@SetGerms.join T a).
Local Notation meet:=(@SetGerms.meet T a).
Local Notation union:=(@set_germ_finite_union T a).

(** Source for [irreducible_variety_binary_union_bound]:
    intersect the two covering variety germs with the
    original irreducible one, supporting 3.4.5, p. 321. *)
Lemma irreducible_variety_binary_union_bound (alpha beta gamma:G):
  IR alpha ->V beta ->V gamma ->set_germ_subset alpha (join beta gamma) ->
  set_germ_subset alpha beta \/set_germ_subset alpha gamma.
Proof.
move=>[hAlpha hIrreducible] hBeta hGamma hContained.
have hDecomposition:alpha=join (meet beta alpha) (meet gamma alpha).
  rewrite -set_germ_distributive set_germ_intersection_commutative;exact:esym hContained.
have [hEqual|hEqual]:=hIrreducible _ _
  (holomorphic_variety_germ_intersection hBeta hAlpha)
  (holomorphic_variety_germ_intersection hGamma hAlpha) hDecomposition.
- left;rewrite hEqual;exact:set_germ_meet_subset_left.
- right;rewrite hEqual;exact:set_germ_meet_subset_left.
Qed.

(** Source for [finite_union_holomorphic_variety_germ]: a
    finite union of actual variety germs remains a variety
    germ, 3.4.5, p. 321. *)
Lemma finite_union_holomorphic_variety_germ (F:seq G):
  (forall beta,beta \in F ->V beta) ->V (union F).
Proof.
elim:F=>[|beta F ih] hV;first exact:holomorphic_variety_germ_empty.
apply:holomorphic_variety_germ_union;first exact:hV beta (mem_head beta F).
apply:ih=>gamma hGamma;apply:hV;by rewrite in_cons hGamma orbT.
Qed.

(** Source for [irreducible_variety_finite_union_bound]: a
    nonempty irreducible germ in a finite union lies in
    some original member, supporting maximal components and
    uniqueness in 3.4.5, p. 321. *)
Theorem irreducible_variety_finite_union_bound (alpha:G) (F:seq G):
  NI alpha ->(forall beta,beta \in F ->V beta) ->set_germ_subset alpha (union F) ->
  exists beta,beta \in F /\set_germ_subset alpha beta.
Proof.
move=>[hIrreducible hNonempty];elim:F=>[|beta F ih] hV hContained.
- exfalso;apply:hNonempty;exact:set_germ_subset_empty hContained.
- have hVF gamma (hGamma:gamma \in F):V gamma.
    apply:hV;by rewrite in_cons hGamma orbT.
  have [hBeta|hF]:=irreducible_variety_binary_union_bound hIrreducible
    (hV beta (mem_head beta F)) (finite_union_holomorphic_variety_germ hVF) hContained.
  + exists beta;split;[exact:mem_head|exact:hBeta].
  + have [gamma [hGamma hBound]]:=ih hVF hF.
    exists gamma;split;last exact:hBound.
    by rewrite in_cons hGamma orbT.
Qed.
End UnionBound.
