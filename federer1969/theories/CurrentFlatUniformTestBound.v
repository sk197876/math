(** Federer (1969), 4.1.12, p. 369:
    a flat current is bounded on
    a family with uniformly bounded comass
    and exterior-derivative comass. Apply the
    original finite flat dual bound on
    its actual compact index. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCoefficientNorms SmoothCompactSet
  SmoothTestSpaces CurrentTestExteriorDerivative CurrentFlatFormSeminormLaws CurrentCompactZerothBounds
  CurrentFlatDualSeminormBasic CurrentFlatNorm FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatUniformTestBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value d := (@current_test_value R h2 n U hU d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation inc d := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU d)).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).

(** Source for [current_flat_uniform_test_bound]:
    every original flat current has a
    finite uniform action bound on tests
    whose comass and derivative comass are
    bounded by a fixed nonnegative c.
    This is the obstruction used for
    the original psi_m in Federer
    4.1.12, p. 369. *)
Theorem current_flat_uniform_test_bound (T:C) c:
  @is_flat_current R h2 n m U hU T->0<=c->
  exists B:R,0<=B /\forall phi:DT,
    (forall x,U x->N m (value m phi x)<=c /\N m.+1 (value m.+1 (d phi) x)<=c)->
    `|@current_value R h2 n U hU m T phi|<=B.
Proof.
move=>[K hFlat] hc.
have hFinite:=@flat_current_supported_finite R h2 n m U hU K T hFlat.
have[a [ha hA]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m T) hFinite.
exists (a*c);split;first exact:mulr_ge0 ha hc.
move=>phi hPoint.
have hTest:@current_flat_test_seminorm R h2 n m U hU K phi<=c.
  rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
    -(@current_test_exterior_derivative_inclusion R h2 n m U hU phi) ge_max.
  apply/andP;split.
  - apply:(@current_compact_zeroth_least_bound R h2 n m U hU K (inc m phi) c hc)=>x hx.
    exact:(hPoint x (smooth_compact_in_domain K x hx)).1.
  - apply:(@current_compact_zeroth_least_bound R h2 n m.+1 U hU K (inc m.+1 (d phi)) c hc)=>x hx.
    exact:(hPoint x (smooth_compact_in_domain K x hx)).2.
have hBound:=@current_flat_dual_finite_bound R h2 n m U hU K
  (@current_value R h2 n U hU m T) a hA phi.
exact:le_trans hBound (ler_wpM2l ha hTest).
Qed.
End CurrentFlatUniformTestBound.
