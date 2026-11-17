(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the regular part exists uniquely by its original
    local manifold condition. This definition assumes no
    stratification or exceptional-set conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric HolomorphicSubmanifoldUP HolomorphicRegularLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_regular_locus_exists]: existence of
    the set defined in 3.4.10, p. 337,
    retaining all original neighbourhood hypotheses. *)
Theorem holomorphic_regular_locus_exists (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)):
  exists L,is_holomorphic_regular_locus m U S L.
Proof.
exists [set a|S a /\exists V:set (coordinate_space (ComplexScalars.C R) n),
    @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) V /\
    V a /\V `<=` U /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m (S `&` V)].
by move=>a.
Qed.

(** Source for [holomorphic_regular_locus_unique]: uniqueness of
    the regular part in 3.4.10, p. 337.
    No chosen chart or defining equation affects it. *)
Theorem holomorphic_regular_locus_unique (R:realType) n m (U S L M:set (coordinate_space (ComplexScalars.C R) n)):
  is_holomorphic_regular_locus m U S L ->
  is_holomorphic_regular_locus m U S M ->L=M.
Proof.
move=>hL hM;apply/seteqP;split=>a;by rewrite hL hM.
Qed.
