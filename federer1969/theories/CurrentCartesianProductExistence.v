(** Federer (1969), 4.1.8, p. 360: on
    the displayed iterated action T(phi_S) is an actual
    continuous current for arbitrary original factors. Existence
    follows from the already proved literal-test-topology
    continuity of the original linear slice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap AlternatingForms
  CurrentSpaces SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology SmoothFunctionSeminormFamily DirectedSeminormFamilyUP
  SeminormFamilyRestriction SeminormFamilyLinearContinuity LinearSubspaceRepresentationUP
  OpenFamilyTopologyUP CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceContinuity ContinuousRealDual NormOpenTopology
  CurrentCartesianSliceFunctionalExistence CurrentCartesianSeparatedSlice CurrentCartesianProductUP
  CurrentCartesianTestProductSealed CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianProductExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation hDC := (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation hDB := (@current_smooth_derivative_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).

Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
(** Source for [current_cartesian_product_exists]: for every
    original S and T there is an actual current on A x B
    satisfying both complete separated-test equations and the
    original iterated-slice action, Federer 4.1.8, p. 360.
    No measure-representability or positive-degree premise is added. *)
Theorem current_cartesian_product_exists
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  exists P:@current_space R h2 (m+n) AB hAB (i+j),
    @is_current_cartesian_product R h2 m n A B hA hB Pure i j S T P /\
    forall phi:DC,@current_value R h2 (m+n) AB hAB (i+j) P phi=
      @current_value R h2 n B hB j T (H S phi).
Proof.
have[P hP]:=@current_cartesian_slice_functional_exists R h2 m n i j A B hA hB S T.
exists P;split;last exact:hP.
split.
- move=>alpha beta;rewrite hP
    (@current_cartesian_separated_slice R h2 m n i j A B hA hB S alpha beta) linearZ.
  reflexivity.
- move=>k l e hDifferent alpha beta;rewrite hP
    (@current_cartesian_separated_slice_off_diagonal R h2 m n i j A B hA hB S k l e
      alpha beta hDifferent) linear0.
  reflexivity.
Qed.
End CurrentCartesianProductExistence.
