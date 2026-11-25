(** Federer (1969), 4.1.11, p. 365: first-projection
    evaluations for the original join boundary calculation.
    Compact cutoffs and the earlier mixed-degree product laws
    suffice; no measure representation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  NormMetric SmoothCompactSet FiniteCoordinates EuclideanBlockLinearMaps CurrentScalarCutoffs
  AlternatingZero CurrentCartesianProjections CurrentCartesianCompactCurrents CurrentCompactMapProper CurrentCartesianFirstCutoffReplacement NormClassOneUP NormRegularity
  CurrentPushforwardSealed CurrentCompactSmoothValue CurrentCompactSmoothAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFirstProjection.
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
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation Image := (fun z (hz:AB z)=>hz.1).
Local Notation hSmooth := (@current_cartesian_first_projection_smooth R m n A B hA hB).
Local Notation ATr := (fun a b (e:a=b)=>@current_degree_transport R h2 m A hA a b e).
Local Open Scope classical_set_scope.
Variables i j:nat.
Variable S:CA i.
Variable T:CB j.
Hypothesis hS:@compact (real_norm_metric_space hNX) (@current_support R h2 m A hA i S).
Hypothesis hT:@compact (real_norm_metric_space hNY) (@current_support R h2 n B hB j T).
Local Notation Proper := (@current_compact_map_proper R h2 (m+n) m (i+j)
  AB A hAB (Product i j S T) p Image (norm_class_continuous (hSmooth 0%N))
  (@current_cartesian_compact_currents R h2 m n i j A B hA hB S T hS hT)).
Local Notation Push := (@CurrentPushforward.value R h2 (m+n) m (i+j)
  AB A hAB hA (Product i j S T) p Image hSmooth Proper).
(** Source for [current_cartesian_compact_first_projection]:
    the original first-projection pushforward of S times T,
    with equal output degrees identified, supporting Federer
    4.1.11, p. 365. Both original current supports are compact. *)
Definition current_cartesian_compact_first_projection k (e:(i+j)%N=k):CA k:=
  ATr _ _ e Push.

(** Source for [current_cartesian_first_projection_cutoff_action]:
    the actual first-projection action uses a scalar cutoff
    equal to one near spt T. This supporting identity gives
    the endpoint terms of Federer 4.1.11, p. 365. *)
Theorem current_cartesian_first_projection_cutoff_action k (e:(i+j)%N=k)
    (gamma:DB 0%N) (W:set Y):
  @open (real_norm_metric_space hNY) W->
  (@current_support R h2 n B hB j T `<=` W)->
  (forall y,W y->@current_test_value R h2 n B hB 0%N gamma y=@zero_form R Y R^o 1)->
  forall alpha:DA k,
    ea k (current_cartesian_compact_first_projection e) alpha=
      ec (i+j) (Product i j S T)
        (Tr _ _ (eq_trans (addn0 k) (esym e)) (Pure k 0 alpha gamma)).
Proof.
case:k /e.
move=>hW hTW hGamma alpha.
rewrite /current_cartesian_compact_first_projection current_degree_transport_identity.
have hProof:eq_trans (addn0 (i+j)) (esym (erefl (i+j)%N))=addn0 (i+j):=
  Prop_irrelevance _ _.
rewrite hProof.
exact:(@CurrentPushforward.laws R h2 (m+n) m (i+j) AB A hAB hA
  (Product i j S T) p Image hSmooth Proper alpha
  (Tr _ _ (addn0 (i+j)) (Pure (i+j) 0 alpha gamma))
  (@current_cartesian_first_cutoff_replacement R h2 m n A B hA hB i j S T
    gamma W hW hTW hGamma alpha)).
Qed.

(** Source for [current_cartesian_first_projection_positive]:
    the first-projection image vanishes when the second current
    has positive degree. This is the endpoint cancellation in
    Federer 4.1.11, p. 365, for arbitrary compact currents. *)
Theorem current_cartesian_first_projection_positive:
  (0<j)%N->current_cartesian_compact_first_projection (erefl (i+j)%N)=0.
Proof.
move=>hj.
pose KT:=@Build_smooth_compact_set R Y NY hNY B
  (@current_support R h2 n B hB j T) (fun y hy=>hy.1) hT.
have[gamma [W [hW [hTW [hWB hGamma]]]]]:=@current_compact_scalar_cutoff R h2 n B hB KT.
have hOff:(i+j)%N<>i.
  move=>hEq.
  have hEqb:(i+j==i+0)%N by apply/eqP;by rewrite addn0.
  have hJ:j=0%N by move:hEqb;rewrite eqn_add2l;exact/eqP.
  by move:hj;rewrite hJ ltnn.
apply:(@current_values_extensional R h2 m (i+j) A hA)=>alpha.
have hAction:=@current_cartesian_first_projection_cutoff_action (i+j)%N
  (erefl (i+j)%N) gamma W hW hTW hGamma alpha.
have hZero:=(@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).2
  (i+j)%N 0%N (eq_trans (addn0 (i+j)) (esym (erefl (i+j)%N))) hOff alpha gamma.
rewrite hZero in hAction.
rewrite hAction linear0 hom_zeroE;reflexivity.
Qed.
End CurrentCartesianFirstProjection.
