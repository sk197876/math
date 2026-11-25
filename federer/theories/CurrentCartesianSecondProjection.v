(** Federer (1969), 4.1.8, p. 360: original mixed tests
    and equal-degree identifications for the product formulas.
    All current and test spaces are the actual opaque spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  NormMetric SmoothCompactSet FiniteCoordinates EuclideanBlockLinearMaps CurrentScalarCutoffs
  AlternatingZero CurrentCartesianProjections CurrentCartesianProjectionProper CurrentCartesianProjectionCutoffReplacement
  CurrentPushforwardSealed CurrentCompactSmoothValue CurrentCompactSmoothAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSecondProjection.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation CC := (fun r=>@current_space R h2 (m+n) AB hAB r).
Local Notation CA := (fun r=>@current_space R h2 m A hA r).
Local Notation CB := (fun r=>@current_space R h2 n B hB r).
Local Notation ec := (fun r=>@current_value R h2 (m+n) AB hAB r).
Local Notation ea := (fun r=>@current_value R h2 m A hA r).
Local Notation eb := (fun r=>@current_value R h2 n B hB r).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation CTr := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).

Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Image := (fun z (hz:AB z)=>hz.2).
Local Notation hSmooth := (@current_cartesian_last_projection_smooth R m n A B hA hB).
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_second_projection]: the
    original q#(S times T) for compact spt S,
    supporting the displayed projection formulas of Federer
    4.1.8, p. 361. Properness on the actual
    product support has already been proved. *)
Definition current_cartesian_second_projection i j (S:CA i) (T:CB j)
    (hCompact:@compact (real_norm_metric_space hNX)
      [set x|@current_support R h2 m A hA i S x]):CB (i+j):=
  @CurrentPushforward.value R h2 (m+n) n (i+j) AB B hAB hB (Product i j S T)
    q Image hSmooth
    (@current_cartesian_projection_proper_on_support R h2 m n i j A B hA hB S T hCompact).

(** Source for [current_cartesian_second_projection_cutoff_action]:
    the actual second-projection pushforward is the original
    product evaluated on a first scalar cutoff and
    the given target test, supporting Federer 4.1.8,
    p. 361. The cutoff equals one near spt S. *)
Theorem current_cartesian_second_projection_cutoff_action i j (S:CA i) (T:CB j)
    (hCompact:@compact (real_norm_metric_space hNX)
      [set x|@current_support R h2 m A hA i S x])
    (gamma:DA 0%N) (W:set X):
  @open (real_norm_metric_space hNX) W->
  (@current_support R h2 m A hA i S `<=` W)->
  (forall x,W x->@current_test_value R h2 m A hA 0%N gamma x=@zero_form R X R^o 1)->
  forall beta:DB (i+j),
    eb (i+j) (@current_cartesian_second_projection i j S T hCompact) beta=
      ec (i+j) (Product i j S T) (Tr _ _ (add0n (i+j)) (Pure 0 (i+j) gamma beta)).
Proof.
move=>hW hSW hGamma beta.
exact:(@CurrentPushforward.laws R h2 (m+n) n (i+j) AB B hAB hB (Product i j S T)
  q Image hSmooth
  (@current_cartesian_projection_proper_on_support R h2 m n i j A B hA hB S T hCompact)
  beta (Tr _ _ (add0n (i+j)) (Pure 0 (i+j) gamma beta))
  (@current_cartesian_projection_cutoff_replacement R h2 m n A B hA hB i j S T
    gamma W hW hSW hGamma beta)).
Qed.

(** Source for [current_cartesian_projection_positive]: q#(S times T)
    is zero whenever spt S is compact and i>0,
    the first original projection formula of Federer 4.1.8,
    p. 361, for arbitrary second-factor currents. *)
Theorem current_cartesian_projection_positive i j (S:CA i) (T:CB j)
    (hCompact:@compact (real_norm_metric_space hNX)
      [set x|@current_support R h2 m A hA i S x]):
  (0<i)%N->@current_cartesian_second_projection i j S T hCompact=0.
Proof.
move=>hi.
pose KA:=@Build_smooth_compact_set R X NX hNX A
  (@current_support R h2 m A hA i S) (fun x hx=>hx.1) hCompact.
have[gamma [W [hW [hSW [hWA hGamma]]]]]:=@current_compact_scalar_cutoff R h2 m A hA KA.
have hOff:0%N<>i.
  move=>hEq;move:hi;by rewrite -hEq ltnn.
apply:(@current_values_extensional R h2 n (i+j) B hB)=>beta.
have hAction:=@current_cartesian_second_projection_cutoff_action i j S T hCompact gamma W
  hW hSW hGamma beta.
have hZero:=(@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).2
  0%N (i+j) (add0n (i+j)) hOff gamma beta.
rewrite hZero in hAction.
rewrite hAction linear0 hom_zeroE;reflexivity.
Qed.

(** Source for [current_cartesian_projection_zero]: when i=0
    and spt S is compact, q#(S times T)=S(1)T,
    the second original projection formula of Federer 4.1.8,
    p. 361. S(1) is the actual smooth-dual
    value of the constant zero-form one. *)
Theorem current_cartesian_projection_zero j (S:CA 0%N) (T:CB j)
    (hCompact:@compact (real_norm_metric_space hNX)
      [set x|@current_support R h2 m A hA 0%N S x]):
  @current_cartesian_second_projection 0%N j S T hCompact=
    (@current_compact_total R h2 m A hA S hCompact)*:T.
Proof.
pose KA:=@Build_smooth_compact_set R X NX hNX A
  (@current_support R h2 m A hA 0%N S) (fun x hx=>hx.1) hCompact.
have[gamma [W [hW [hSW [hWA hGamma]]]]]:=@current_compact_scalar_cutoff R h2 m A hA KA.
have hScalar:=@current_compact_total_cutoff R h2 m A hA S hCompact gamma W hW hSW hWA hGamma.
apply:(@current_values_extensional R h2 n j B hB)=>beta.
have hAction:=@current_cartesian_second_projection_cutoff_action 0%N j S T hCompact gamma W
  hW hSW hGamma beta.
rewrite current_test_degree_transport_identity
  ((@CartesianCurrentProduct.laws R h2 m n 0%N j A B hA hB S T).1 gamma beta) hScalar in hAction.
have hRight:eb j ((@current_compact_total R h2 m A hA S hCompact)*:T) beta=
    (@current_compact_total R h2 m A hA S hCompact)*eb j T beta.
  change (@current_point_evaluation R h2 n j B hB beta
    ((@current_compact_total R h2 m A hA S hCompact)*:T)=
    (@current_compact_total R h2 m A hA S hCompact)*:
      @current_point_evaluation R h2 n j B hB beta T).
  exact:(linZ (hom_linear (@current_point_evaluation R h2 n j B hB beta))
    (@current_compact_total R h2 m A hA S hCompact) T).
exact:(eq_trans hAction (esym hRight)).
Qed.
End CurrentCartesianSecondProjection.
