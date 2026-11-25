(** Actual-space regressions for Federer (1969), 4.1.11,
    pp. 365–366: a nonzero point current in R^0 has
    a zero positive-degree join; the empty rectangle
    remains nonzero; repeated vertices vanish in an
    actual R^1 simplex. No nondegeneracy is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentDirac CurrentDiracDensity DiracCurrentBounds CurrentAboveDimension
  CurrentCompactElementaryPushforwards CurrentJoinSealed CurrentJoinLaws CurrentFullRectangle
  EuclideanFundamentalCurrentPoint OrientedSimplexCurrentSealed CurrentJoins.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section JoinCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R 0%N)) x).
Local Notation P := (@dirac_current R h2 0%N Full hFull (0:X)).
Local Notation hP := (@current_compact_dirac_support R h2 0%N Full hFull (0:X) Logic.I).

(** Source for [join_point_source_nonzero]: the original
    point base [u]=delta_u is nonzero even in R^0,
    checking Federer 4.1.11, p. 365. An actual
    compact test of value one witnesses nonvanishing. *)
Example join_point_source_nonzero:P<>0.
Proof.
move=>hZero.
have [psi hPsi]:=@dirac_current_unit_test R h2 0%N Full hFull (0:X) Logic.I.
have hOne : @current_value R h2 0%N Full hFull 0%N P psi = 1 := hPsi.
rewrite hZero (linear0 (@current_value R h2 0%N Full hFull 0%N)) hom_zeroE in hOne.
have hBad : (1:R) = 0 := esym hOne.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

(** Source for [zero_dimensional_point_join_zero]: the
    actual join of the nonzero R^0 point with itself
    has degree one and is zero, checking the original
    arbitrary dimensions in Federer 4.1.11, p. 365. *)
Example zero_dimensional_point_join_zero:
  @CurrentJoin.value R h2 0%N 0%N 0%N P P hP hP=0.
Proof. exact:(@current_join_above_dimension R h2 0%N 0%N 0%N P P hP hP (ltn0Sn 0%N)). Qed.

(** Source for [empty_rectangle_is_nonzero]: the actual
    empty rectangle is the nonzero degree-zero point,
    checking the 0!=1 endpoint of the rectangular
    decomposition in Federer 4.1.11, p. 366. *)
Example empty_rectangle_is_nonzero:
  @current_full_rectangle R h2 [::] Logic.I<>0.
Proof.
rewrite current_full_rectangle_empty euclidean_fundamental_current_point.
exact:join_point_source_nonzero.
Qed.

(** Source for [coincident_line_simplex_zero]: the actual
    one-dimensional simplex with two equal R^1 vertices
    vanishes, checking the degenerate factors retained
    in Federer 4.1.11, pp. 365–366. *)
Example coincident_line_simplex_zero:
  @OrientedSimplexCurrent.value R h2 1%N 1%N (fun _:'I_2=>(0:R_n R 1%N))=0.
Proof.
apply:(@oriented_simplex_current_repeated_vertices R h2 1%N 1%N
  (fun _:'I_2=>(0:R_n R 1%N)) ord0 (lift ord0 ord0));last by [].
by rewrite -val_eqE /=.
Qed.
End JoinCurrentEndpointExamples.
