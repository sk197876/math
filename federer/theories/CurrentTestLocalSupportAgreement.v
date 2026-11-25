(** Federer (1969), 4.1.18, p. 374: the
    support comparison for the averaged homotopy can
    be checked near each support point. The union
    of those neighbourhoods gives the original
    near-support criterion of 4.1.7.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentTestNearSupportAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestLocalSupportAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation X:=(R_n R n).
Local Notation XT:=(real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
Local Notation D:=(@current_test_space R h2 n U hU m).
Local Notation value:=(@current_test_value R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.

(** Source for [current_test_local_support_values_equal]:
    the original support argument, 4.1.7, p. 359,
    used in the smoothing construction of 4.1.18,
    p. 374. Pointwise agreement alone is not used. *)
Theorem current_test_local_support_values_equal (phi psi:D):
  (forall x,@current_support R h2 n U hU m T x->
    exists W:set X,@open XT W /\W x /\
      forall y,W y->value phi y=value psi y) ->
  @current_value R h2 n U hU m T phi=
  @current_value R h2 n U hU m T psi.
Proof.
move=>hLocal.
pose Good:set (set X):=[set W|@open XT W /\
  forall y,W y->value phi y=value psi y].
pose O:set X:=\bigcup_(W in Good) W.
have hO:@open XT O by apply:bigcup_open=>W hW;exact:hW.1.
apply:(@current_test_near_support_values_equal R h2 n m U hU T phi psi O hO).
- move=>x hx;have[W [hW [hxW hMatch]]]:=hLocal x hx.
  exists W;last exact:hxW.
  exact:conj hW hMatch.
- move=>y [W hW hy];exact:hW.2 y hy.
Qed.
End CurrentTestLocalSupportAgreement.
