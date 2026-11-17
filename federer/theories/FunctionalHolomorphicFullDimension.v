(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.5, p. 321: the
    explicit n=m convention for functional holomorphic submanifolds
    leaves only the original nonvanishing inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP Hom FiniteIndependence GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric HolomorphicUP FunctionalHolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_full_dimension]: in
    case n=m the original S is precisely U minus the
    zero set of one holomorphic g, 3.4.5, p. 321. *)
Lemma functional_holomorphic_full_dimension (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)):
  is_functional_holomorphic_submanifold n U S <->
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) U /\
  exists g:coordinate_space (ComplexScalars.C R) n->ComplexScalars.C R,
    @is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o (@holomorphic_coordinate_norm R n)
      (@complex_modulus R) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
      (@complex_modulus_real_norm R) U g /\forall x,S x <->U x /\g x<>0.
Proof.
have hEmpty (i:'I_(n-n)):False.
  have hBound:(n-n<=0)%N by rewrite subnn.
  have hh:=leq_trans (ltn_ord i) hBound.
  by move:hh;rewrite ltn0.
split.
- move=>[_ [hU [f [g [hf [hg [hS hD]]]]]]].
  split;first exact:hU.
  exists g;split;first exact:hg.
  move=>x;rewrite hS;split.
  + by move=>[hx [_ hNonzero]];split.
  + move=>[hx hNonzero];split;first exact:hx.
    split;last exact:hNonzero.
    move=>i;exfalso;exact:hEmpty i.
- move=>[hU [g [hg hS]]].
  split;first exact:leqnn.
  split;first exact:hU.
  exists (fun (_:'I_(n-n)) (_:coordinate_space (ComplexScalars.C R) n)=>(0:ComplexScalars.C R)),g;split.
  + move=>i;exfalso;exact:hEmpty i.
  + split;first exact:hg.
    split.
    * move=>x;rewrite hS;split.
      -- move=>[hx hNonzero];split;first exact:hx.
         split;last exact:hNonzero.
         move=>i;exfalso;exact:hEmpty i.
      -- by move=>[hx [_ hNonzero]];split.
    * move=>x hx;exists (fun _=>0);split.
      -- move=>i;exfalso;exact:hEmpty i.
      -- move=>c hc i;exfalso;exact:hEmpty i.
Qed.
