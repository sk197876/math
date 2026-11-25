(** Federer (1969), 4.1.24, p. 381: the
    finitely many points of an integral polyhedral
    zero-current admit original unit-comass test coordinates.
    Use the already proved finite metric separation
    and bounded compact neighbourhood tests on U.
    Empty finite families and R^0 remain included. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingZero CurrentSpaces CurrentZeroCovectorMaps CurrentCoefficientNorms
  CurrentSupportGeometry CurrentFormSupportValues SmoothTestSpaces
  SmoothCompactSet FiniteMetricSeparation MetricClosedBalls CurrentOpenBoundedNeighbourhoodTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [current_finite_point_test_basis_exists]: original
    scalar test coordinates on every prescribed finite
    subset of U, with exact Kronecker values and
    comass at most one, 4.1.24, p. 381. *)
Theorem current_finite_point_test_basis_exists (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (H:{fset R_n R n}):
  (forall x,x\in H->U x)->
  exists gamma:H->@current_test_space R h2 n U hU 0%N,
    (forall i j:H,zero_form_value
      (@current_test_value R h2 n U hU 0%N (gamma i) (val j))=
      if i==j then 1 else 0) /\
    forall (i:H) x,U x->@current_form_comass R h2 n 0%N
      (@current_test_value R h2 n U hU 0%N (gamma i) x)<=1.
Proof.
move=>hHU.
pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hNX.
pose DT:=@current_test_space R h2 n U hU 0%N.
pose hE:=@current_smooth_space_laws R h2 n U hU 0%N.
have hUOpen:@open XT U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have[e [he hSeparate]]:=@finite_metric_points_separated R XT H.
pose r:=e/2.
have hr:0<r by rewrite /r divr_gt0 //;lra.
have hHalf:forall t:R,e<=t->t<r->False by rewrite /r=>t h1 h3;lra.
have hChoices (i:H):exists gamma:DT,
    (forall j:H,zero_form_value (@current_test_value R h2 n U hU 0%N gamma (val j))=
      if i==j then 1 else 0) /\
    forall x,U x->@current_form_comass R h2 n 0%N
      (@current_test_value R h2 n U hU 0%N gamma x)<=1.
  pose W:set X:=U `&` [set x|@mdist R XT (val i) x<r].
  have hW:@open XT W:=openI hUOpen (@metric_open_ball_open R XT (val i) r).
  pose K:=@Build_smooth_compact_set R X NX hNX U [set val i]
    (fun x hx=>eq_ind_r U (hHU (val i) (valP i)) hx) (@compact_set1 XT (val i)).
  have hKW:smooth_compact_carrier K `<=` W.
    move=>x ->;split;first exact:(hHU (val i) (valP i)).
    change (is_true (@mdist R XT (val i) (val i)<r));by rewrite mdistxx.
  have[gamma [hSupport [hRange hOne]]]:=@current_open_bounded_neighbourhood_test_exists
    R h2 n U hU K W hW (fun x hx=>hx.1) hKW.
  exists gamma;split.
  - move=>j;case:(eqVneq i j)=>[hIJ|hIJ].
    + rewrite -hIJ (hOne (val i) (erefl _)) ?eqxx;exact:zero_formK.
    + rewrite ?(negPf hIJ).
      have hDifferent:val i!=val j by rewrite (inj_eq val_inj).
      have hSep:=hSeparate (val i) (val j) (valP i) (valP j) hDifferent.
      have hOutside:~@current_test_support R h2 n 0%N U hU gamma (val j).
        move=>hSupp;have hNear:@mdist R XT (val i) (val j)<r:=(hSupport (val j) hSupp).2.
        exact:(hHalf _ hSep hNear).
      have hZero:=@current_form_value_outside_support R h2 n 0%N U hU
        (smooth_test_inclusion hE gamma) (val j) (hHU (val j) (valP j)) hOutside.
      have hValue:@current_test_value R h2 n U hU 0%N gamma (val j)=
          @current_smooth_value R h2 n U hU 0%N (smooth_test_inclusion hE gamma) (val j).
        by [].
      by rewrite hValue hZero linear0.
  - move=>x hx;rewrite (@current_zero_form_coefficient_norm R h2 n
      (@current_test_value R h2 n U hU 0%N gamma x)).
    have h:=hRange x hx.
    rewrite (ger0_norm (andP h).1);exact:(andP h).2.
have[gamma hGamma]:=choice hChoices.
exists gamma;split;[move=>i;exact:(hGamma i).1|move=>i;exact:(hGamma i).2].
Qed.
