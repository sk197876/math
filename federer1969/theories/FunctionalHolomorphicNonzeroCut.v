(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 334–335:
    imposing the additional holomorphic inequality chi!=0
    preserves the original functional holomorphic manifold
    and its dimension. Keep the actual defining
    equations and their independent differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP HolomorphicUP HolomorphicProduct
  FunctionalHolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_nonzero_cut]:
    the original D=Z intersect {chi composed
    with P_m!=0} remains a functional holomorphic
    m-submanifold, 3.4.12, p. 339, extending 3.4.8(11), pp. 334–335.
    Multiplication combines the two nonvanishing conditions;
    no new differential hypothesis is introduced. *)
Theorem functional_holomorphic_nonzero_cut (R:realType) n m
    (U S:set (coordinate_space (ComplexScalars.C R) n)) (chi:coordinate_space (ComplexScalars.C R) n->(ComplexScalars.C R)^o):
  @is_functional_holomorphic_submanifold R n m U S ->
  @is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o (@holomorphic_coordinate_norm R n)
    (@complex_modulus R) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
    (@complex_modulus_real_norm R) U chi ->
  @is_functional_holomorphic_submanifold R n m U [set x|S x /\chi x<>0].
Proof.
move=>[hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]] hChi.
split;first exact:hMN.
split;first exact:hU.
exists f,(fun x=>g x*chi x);split;first exact:hF.
split;first exact:holomorphic_product hG hChi.
split.
- move=>x;split.
  + move=>[/hEquation [hx [hZero hNonzero]] hChiX];split;first exact:hx.
    split;first exact:hZero.
    apply/eqP;rewrite mulf_eq0;apply/negP=>/orP [/eqP h|/eqP h].
    * exact:hNonzero h.
    * exact:hChiX h.
  + move=>[hx [hZero hNonzero]];split.
    * apply/(hEquation x);split;first exact:hx.
      split;first exact:hZero.
      move=>h;apply:hNonzero;by rewrite h mul0r.
    * move=>h;apply:hNonzero;by rewrite h mulr0.
- move=>x [hx hNonzero];exact:hDifferentials x hx.
Qed.
