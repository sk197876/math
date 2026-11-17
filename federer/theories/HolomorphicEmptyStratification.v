(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327:
    an empty difference has the empty
    stratum family. Every boundary requirement is
    then vacuous, with no chosen geometric
    object or dimension convention added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP SetGermSealed HolomorphicFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_empty_stratification]:
    the trivial empty-difference case of
    3.4.12, p. 339, extending 3.4.8(11), p. 327. *)
Theorem holomorphic_empty_stratification (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    m (U0 S0:set (coordinate_space (ComplexScalars.C R) n)):
  @SetGerms.meet (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) alpha (@SetGerms.neg (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) beta) = @set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) set0 ->
  @is_holomorphic_finite_stratification R n alpha beta m U0 S0 0
    (fun _=>set0) (fun _=>set0) (fun _=>set0).
Proof.
move=>hEmpty.
have hImpossible (i:'I_0):False by have:=ltn_ord i;rewrite ltn0.
constructor;try (move=>i;exfalso;exact:hImpossible i).
have hUnion:(\bigcup_(i:'I_0) (@set0 (coordinate_space (ComplexScalars.C R) n))) = set0.
  apply/seteqP;split=>x;last by [].
  by move=>[i _ _];exact:hImpossible i.
by rewrite hUnion.
Qed.
