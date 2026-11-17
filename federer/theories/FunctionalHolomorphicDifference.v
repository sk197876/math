(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.9, p. 337:
    the original functional holomorphic stratum is the
    difference of two holomorphic subvarieties of its domain.
    Keep its original finite equations and inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FunctionalHolomorphicSubmanifoldUP FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_difference]: the difference
    representation used to apply the first assertion
    of 3.4.9, p. 337, to each original
    stratum and its holomorphic sphere cut. *)
Theorem functional_holomorphic_difference (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_functional_holomorphic_submanifold R n m U S ->
  exists H N:set (coordinate_space (ComplexScalars.C R) n),
    @is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) U H /\
    @is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) U N /\S=H `\` N.
Proof.
move=>[hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]].
pose X:=coordinate_space (ComplexScalars.C R) n.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose H:set X:=[set x|U x /\forall i,f i x=0].
pose Z:set X:=[set x|U x /\g x=0].
have hH:@is_finite_holomorphic_variety R X NX hNX U H.
  split;first exact:hU.
  exists (Finite.clone 'I_(n-m) _),f;by split.
have hZ:@is_finite_holomorphic_variety R X NX hNX U Z.
  split;first exact:hU.
  exists (Finite.clone 'I_1 _),(fun _=>g);split;first by move=>i;exact:hG.
  move=>x;split;first by move=>[hx hZero];split=>// i.
  by move=>[hx hZero];split;last exact:hZero ord0.
exists H,(H `&` Z);split;first exact:hH.
split;first exact:finite_holomorphic_variety_intersection hH hZ.
apply/seteqP;split.
- move=>x /hEquation [hx [hZero hNonzero]];split;first by split.
  by move=>[_ [_ hBad]];apply:hNonzero.
- move=>x [[hx hZero] hNot];apply/(hEquation x);split;first exact:hx.
  split;first exact:hZero.
  move=>hBad;apply:hNot;split;by split.
Qed.
