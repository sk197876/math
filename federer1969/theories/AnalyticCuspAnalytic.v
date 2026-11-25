(** Federer (1969), 3.4.11, p. 338:
    the original cusp is an actual analytic
    variety on the whole plane. Its original polynomial
    is analytic by the proved scalar coordinate calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormAnalyticUP NormAnalyticOperations NormAnalyticScalarProducts
  EuclideanScalarCoordinateAnalytic FiniteAnalyticVarietyUP AnalyticVarietyGermUP
  AnalyticCuspUP AnalyticCuspSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_equation_analytic]: the
    defining polynomial y^2-x^3 of the original
    example, 3.4.11, p. 338. *)
Lemma analytic_cusp_equation_analytic (R:realType):
  @norm_analytic R (R_n R 2) R^o (inner_norm (@euclidean_inner_productP R 2))
    (fun t:R^o=>`|t|) (inner_norm_real_norm (@euclidean_inner_productP R 2))
    (@scalar_absolute_value_norm R) setT
    (fun v=>(v ord_max)^+2-(v ord0)^+3).
Proof.
exact:(norm_analytic_subtract
  (norm_analytic_scalar_power 2%N (@euclidean_scalar_coordinate_analytic R 2 ord_max))
  (norm_analytic_scalar_power 3%N (@euclidean_scalar_coordinate_analytic R 2 ord0))).
Qed.

(** Source for [analytic_cusp_finite_variety]: the exact
    original cusp is a finite analytic variety,
    3.4.11, p. 338. *)
Theorem analytic_cusp_finite_variety (R:realType):
  @is_finite_analytic_variety R (R_n R 2) (inner_norm (@euclidean_inner_productP R 2))
    (inner_norm_real_norm (@euclidean_inner_productP R 2)) setT (@AnalyticCusp.set R).
Proof.
split;first exact:openT.
exists (Finite.clone unit _),(fun (_:unit) (v:R_n R 2)=>(v ord_max)^+2-(v ord0)^+3).
split;first by move=>i;exact:analytic_cusp_equation_analytic.
move=>v;rewrite (@AnalyticCusp.laws R v);split.
- move=>h;split;first exact:Logic.I;by move=>i;rewrite h subrr.
- move=>[_ h];have hEq:=h tt.
  move/eqP:hEq;rewrite subr_eq0 eq_sym=>/eqP;done.
Qed.
