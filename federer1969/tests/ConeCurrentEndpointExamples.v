(** Actual-space boundary regression for Federer (1969), 4.1.10,
    p. 364: a nonzero zero-current in R^0 has total one and a zero
    degree-one cone. The degree-zero case retains its point term;
    the positive top-degree conclusion must not erase that term. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingZero CurrentSpaces CurrentEvaluation
  CurrentConstantFields CurrentCompactSmoothValue CurrentDirac CurrentDiracDensity DiracCurrentBounds
  PointMultivectorCurrentSealed PointMultivectorCurrentSupport PointMultivectorCurrentSmooth
  CurrentHomotopyUP CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentAboveDimension
  CurrentOpenConeSealed CurrentConeSegmentHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ConeCurrentEndpointExamples.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation U := (fun _:X => True).
Local Notation hOpen := (fun (x:X) (_:True) => @norm_full_domain_interior R X NX x).
Local Notation A := (fun _:R => True).
Local Notation h := (@CurrentConeHomotopy.value R 0%N (0:X)).
Local Notation hH := (@current_cone_ambient_homotopy R 0%N (0:X) U hOpen).
Local Notation hU := (@current_homotopy_source_open R 0%N 0%N A U U
  (fun _:X => 0) (fun x:X => x) h hH.1).
Local Notation unit := (@current_scalar_multivector_unit R 0%N).

(** Source for [zero_dimensional_cone_point_current]: the actual
    unit point current in the degree-zero case of Federer 4.1.10,
    p. 364. It uses the original sealed point-current operation. *)
Definition zero_dimensional_cone_point_current : @current_space R h2 0%N U hU 0%N :=
  @PointMultivectorCurrent.value R h2 0%N 0%N U hU (0:X) Logic.I unit.
Local Notation T := zero_dimensional_cone_point_current.
Local Notation hCompact := (@point_multivector_current_compact R h2 0%N 0%N U hU (0:X) Logic.I unit).
Local Notation cone := (@CurrentOpenCone.value R h2 0%N 0%N U hOpen (0:X) T hCompact).

(** Source for [zero_dimensional_cone_point_dirac]: the actual
    scalar-unit point pairing is the original delta_0, supporting
    the degree-zero term in Federer 4.1.10, p. 364. This comparison
    is independent of the cone identity being checked. *)
Lemma zero_dimensional_cone_point_dirac : T=@dirac_current R h2 0%N U hU (0:X).
Proof.
apply: current_values_extensional => psi.
by rewrite (@PointMultivectorCurrent.laws R h2 0%N 0%N U hU (0:X) Logic.I unit psi)
  current_scalar_multivector_unit_pairing dirac_current_evaluation.
Qed.

(** Source for [zero_dimensional_cone_source_nonzero]: the
    original zero-dimensional point current is nonzero, supporting
    the distinct degree-zero case in Federer 4.1.10, p. 364. An
    independently proved actual unit test witnesses nonvanishing. *)
Example zero_dimensional_cone_source_nonzero : T<>0.
Proof.
move=> hZero.
have [psi hPsi] := @dirac_current_unit_test R h2 0%N U hU (0:X) Logic.I.
have hOne : @current_value R h2 0%N U hU 0%N T psi = 1.
  by rewrite zero_dimensional_cone_point_dirac.
rewrite hZero (linear0 (@current_value R h2 0%N U hU 0%N)) hom_zeroE in hOne.
have hBad : (1:R)=0 := esym hOne.
by have := @oner_neq0 R; rewrite hBad eqxx.
Qed.

(** Source for [zero_dimensional_cone_total_one]: the actual
    original smooth extension gives T(1)=1 for the nonzero R^0
    point current, checking the literal coefficient in Federer
    4.1.10, p. 364. No normalization is assumed as a hypothesis. *)
Example zero_dimensional_cone_total_one :
  @current_compact_total R h2 0%N U hU T hCompact = 1.
Proof.
rewrite /current_compact_total
  (@point_multivector_current_smooth_value R h2 0%N 0%N U hU (0:X) Logic.I unit)
  (@current_constant_form_values R h2 0%N U hU 0%N (@zero_form R X R^o 1) (0:X) Logic.I)
  current_scalar_multivector_unit_pairing zero_formK.
by [].
Qed.

(** Source for [zero_dimensional_point_cone_zero]: the original
    cone of the actual nonzero R^0 point current has degree one
    and vanishes, checking the above-dimension step of Federer
    4.1.10, p. 364, without concluding that its source is zero. *)
Example zero_dimensional_point_cone_zero : cone=0.
Proof.
exact: (@current_above_dimension R h2 0%N 1%N (ltn0Sn 0%N) U hU cone).
Qed.
End ConeCurrentEndpointExamples.
