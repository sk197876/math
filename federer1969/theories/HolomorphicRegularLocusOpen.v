(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the original regular locus is relatively open
    in the original holomorphic set, directly by its
    local manifold definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric HolomorphicSubmanifoldUP HolomorphicRegularLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_regular_locus_open_form]: relative
    openness of the regular part of 3.4.10,
    p. 337. The original regular manifold witness
    at one point also works at every point
    of its intersection with S. *)
Theorem holomorphic_regular_locus_open_form (R:realType) n m (U S L:set (coordinate_space (ComplexScalars.C R) n)):
  is_holomorphic_regular_locus m U S L ->
  exists W:set (coordinate_space (ComplexScalars.C R) n),
    @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) W /\
    W `<=` U /\L=S `&` W.
Proof.
move=>hL.
pose D:set (set (coordinate_space (ComplexScalars.C R) n)):=fun V=>
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) V /\
  V `<=` U /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m (S `&` V).
exists (\bigcup_(V in D) V);split.
- apply:bigcup_open=>V hV;exact:hV.1.
split.
- move=>x [V hV hx];exact:hV.2.1 x hx.
- apply/seteqP;split.
  + move=>a /hL [ha [V [hOpen [haV [hInside hManifold]]]]].
    split;first exact:ha.
    exists V;last exact:haV;by split=>//;split.
  + move=>a [ha [V [hOpen [hInside hManifold]] haV]].
    apply/hL;split;first exact:ha.
    exists V;by split=>//;split=>//;split.
Qed.
