(** Federer (1969), 3.4.8(11), p. 334:
    the original later B_j witnesses supply
    the finite actual prepared equation family.
    Its laws were specified independently; the
    original preparation theorem supplies existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology NormAnalyticUP
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticPrefixCoordinatesSealed AnalyticRotatedGermIdeal
  CommutativeIdealUP AnalyticReductionActual AnalyticReductionPreparedEquation AnalyticPreparedTailUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TailExistence.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation Y:=(fun j:'I_n=>R_n R j).
Local Notation NY:=(fun j:'I_n=>inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(fun j:'I_n=>inner_norm_real_norm (@euclidean_inner_productP R j)).
Variable I:set (@analytic_germ_ring R X NX hNX 0).
Variable g:@orthogonal_group R X B hB n e he.
Variable m:nat.
(** Source for [analytic_prepared_reduction_tail_exists]:
    the entire original W_j family used
    in 3.4.8(11), pp. 334–335.
    Each active witness is prepared by the
    earlier original-centre theorem. Inactive equations
    are the actual zero germ. Every choice
    remains a local witness behind these laws. *)
Theorem analytic_prepared_reduction_tail_exists:
  is_commutative_ideal I ->~I 1 ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  exists degree:'I_n->nat,exists U:forall j:'I_n,set (Y j),
    exists b:forall j:'I_n,'I_(degree j)->@analytic_representative_type R (Y j) (NY j) (hNY j) 0,
    exists f:'I_n->@analytic_representative_type R X NX hNX 0,
      @is_analytic_prepared_reduction_tail R X B hB n e he omega I g m degree U b f.
Proof.
move=>hI hProper hTail.
have hIg:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
have hExists j:exists k,exists (U:set (Y j))
    (b:'I_k->@analytic_representative_type R (Y j) (NY j) (hNY j) 0)
    (f:@analytic_representative_type R X NX hNX 0),
  @analytic_rotated_germ_ideal R X B hB n e he I g (analytic_germ f) /\
  ((m<=j)%N ->(0<k)%N /\U 0 /\@open (real_norm_metric_space (hNY j)) U /\
    (forall i,@norm_analytic R (Y j) R^o (NY j) (fun z:R^o=>`|z|) (hNY j)
      (@scalar_absolute_value_norm R) U (analytic_representative_value (b i))) /\
    (forall i,analytic_representative_value (b i) 0 = 0) /\
    forall x,analytic_representative_value f x = (omega j x)^+k+
      \sum_(i<k) analytic_representative_value (b i)
        (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
          (leq_trans (leqnSn (j:nat)) (ltn_ord j)) x)*(omega j x)^+(i:nat)).
  case hActive:(m<=j)%N.
  - have [k [U [b [f [hK [hU0 [hOpen [hAnalytic [hZero [hMember hFormula]]]]]]]]]]:=
      @analytic_reduction_prepared_equation R X B hB n e he omega hDual I g j
        hI hProper (hTail j hActive).
    exists k,U,b,f;split;first exact:hMember.
    move=>_;split;first exact:hK.
    split;first exact:hU0.
    split;first exact:hOpen.
    split;first exact:hAnalytic.
    by split.
  - exists 0%N,setT,
      (fun _:'I_0=>@analytic_constant_representative R (Y j) (NY j) (hNY j) 0 0),
      (@analytic_constant_representative R X NX hNX 0 0).
    split.
    + change (@analytic_rotated_germ_ideal R X B hB n e he I g 0).
      exact:commutative_ideal_zero hIg.
    + by move=>hImpossible.
pose Data:=fun j:'I_n=>{k:nat & {U:set (Y j) &
  {b:'I_k->@analytic_representative_type R (Y j) (NY j) (hNY j) 0 &
    @analytic_representative_type R X NX hNX 0}}}.
pose valid:=fun (j:'I_n) (d:Data j)=>
  let k:=projT1 d in let U:=projT1 (projT2 d) in
  let b:=projT1 (projT2 (projT2 d)) in let f:=projT2 (projT2 (projT2 d)) in
  @analytic_rotated_germ_ideal R X B hB n e he I g (analytic_germ f) /\
  ((m<=j)%N ->(0<k)%N /\U 0 /\@open (real_norm_metric_space (hNY j)) U /\
    (forall i,@norm_analytic R (Y j) R^o (NY j) (fun z:R^o=>`|z|) (hNY j)
      (@scalar_absolute_value_norm R) U (analytic_representative_value (b i))) /\
    (forall i,analytic_representative_value (b i) 0 = 0) /\
    forall x,analytic_representative_value f x = (omega j x)^+k+
      \sum_(i<k) analytic_representative_value (b i)
        (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
          (leq_trans (leqnSn (j:nat)) (ltn_ord j)) x)*(omega j x)^+(i:nat)).
have hPacked j:exists d:Data j,@valid j d.
  have [k [U [b [f hGood]]]]:=hExists j.
  exists (existT _ k (existT _ U (existT _ b f)));exact:hGood.
pose data:=fun j=>projT1 (cid (hPacked j)).
have hData j:@valid j (data j):=projT2 (cid (hPacked j)).
pose degree:=fun j=>projT1 (data j).
pose U:=fun j=>projT1 (projT2 (data j)).
pose b:=fun j=>projT1 (projT2 (projT2 (data j))).
pose f:=fun j=>projT2 (projT2 (projT2 (data j))).
exists degree,U,b,f;constructor.
- move=>j;exact:(hData j).1.
- move=>j hj;exact:((hData j).2 hj).1.
- move=>j hj;split;[exact:((hData j).2 hj).2.1|exact:((hData j).2 hj).2.2.1].
- move=>j hj;exact:((hData j).2 hj).2.2.2.1.
- move=>j hj;exact:((hData j).2 hj).2.2.2.2.1.
- move=>j hj;exact:((hData j).2 hj).2.2.2.2.2.
Qed.
End TailExistence.
