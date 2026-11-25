(** Federer (1969), 4.1.12, p. 368: finitely
    many isolated support points admit an actual
    bounded smooth test equal to one there
    and zero at all other points of
    the original set. Use the preceding
    bounded neighbourhood cutoff on their finite compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AlternatingForms AlternatingZero CurrentSpaces CurrentSupportGeometry CurrentZeroCovectorMaps
  SmoothCompactSet CurrentBoundedNeighbourhoodTest SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFiniteIsolatedTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (@current_test_space R h2 n Full hFull 0%N).
Local Notation value := (@current_test_value R h2 n Full hFull 0%N).
Variable A:set X.
Variable I:finType.
Variable a:I->X.

(** Source for [current_finite_isolated_test_exists]:
    a finite family of points isolated in
    A has an original scalar test with
    values in [0,1], value one on
    that family and value zero on
    every other point of A. This
    supports the infinite-mass assertion in Federer
    4.1.12, p. 368; the family may be empty. *)
Theorem current_finite_isolated_test_exists:
  (forall i,exists W:set X,@open XT W /\W (a i) /\
    forall z,A z->W z->z=a i)->
  exists gamma:DT,
    (forall x,0<=@current_zero_form_coefficient R n (value gamma x)<=1) /\
    (forall i,value gamma (a i)=@zero_form R X R^o 1) /\
    forall x,A x->~(a @` setT) x->value gamma x=0.
Proof.
move=>hIsolated.
have[W hW]:=choice hIsolated.
pose V:set X:=\bigcup_i W i.
have hOpen:@open XT V by apply:bigcup_open=>i _;exact:(hW i).1.
have hFinite:finite_set (a @` setT):=finite_image a (@finite_finset I setT).
pose K:=@Build_smooth_compact_set R X NX hNX Full (a @` setT)
  (fun _ _=>Logic.I) (@finite_compact XT (a @` setT) hFinite).
have hKV:smooth_compact_carrier K `<=` V.
  move=>x [i _ <-];exists i;first exact:Logic.I.
  exact:(hW i).2.1.
have[gamma [hSupport [hRange hOne]]]:=@current_bounded_neighbourhood_test_exists R h2 n K V hOpen hKV.
exists gamma;split;first exact:hRange.
split.
- move=>i;apply:hOne;by exists i.
- move=>x hx hNotSelected;apply:contrapT=>hNonzero.
  have hIn:@current_test_support R h2 n 0%N Full hFull gamma x.
    exact:(@smooth_function_nonzero_in_support R X (A_m X R^o 0%N) NX hNX Full DT
      value gamma x Logic.I hNonzero).
  have[i _ hIx]:=hSupport x hIn.
  apply:hNotSelected;exists i;first exact:Logic.I.
  exact:esym ((hW i).2.2 x hx hIx).
Qed.
End CurrentFiniteIsolatedTest.
