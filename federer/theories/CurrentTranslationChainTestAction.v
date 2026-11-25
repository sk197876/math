(** Federer (1969), 4.1.18, p. 374: the
    actual fixed-z deformation acts by the old
    transgression on every compact representative near
    the original support. The input and output
    remain in their original canonical whole-space
    presentations.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport CurrentEqualDomainTests
  SmoothTestSpaces SmoothTestEvaluation CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentHomotopyTestReplacementUP
  CurrentDeformationChainTestAction CurrentTranslationChain CurrentTranslationHomotopy
  CurrentTranslations EuclideanAdditiveGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationChainTestAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable z:X.
Local Notation tau:=(@euclidean_translation R n z).
Local Notation H:=(@current_translation_homotopy R n z).
Local Notation hH:=(@current_translation_homotopy_laws R n z).
Local Notation hSource:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation TargetTest:=(@current_test_space R h2 n Full hFull (1+m)%N).
Local Notation SourceTest:=(@current_test_space R h2 n Full hFull m).
Local Notation TargetRawTest:=(@current_test_space R h2 n Full hTarget (1+m)%N).
Local Notation RawOmega:=(fun omega:TargetTest=>
  @current_test_equal_domain R h2 n (1+m)%N Full Full hFull hTarget (erefl _) omega).
Local Notation Inc:=(smooth_test_inclusion
  (@current_smooth_space_laws R h2 n Full hTarget (1+m)%N)).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 n n m
  (fun _=>True) Full Full (fun x:X=>x) tau H hH).
Local Notation ev:=(@current_smooth_value R h2 n Full hSource m).
Variable T:@current_space R h2 n Full hFull m.

(** Source for [current_translation_chain_test_action]: the
    compact-test restatement of the original H^z
    chain, by 4.1.9, p. 363, used in
    the defining average of 4.1.18, p. 374. *)
Theorem current_translation_chain_test_action
    (omega:TargetTest) (beta:SourceTest) (W:set X):
  @open (real_norm_metric_space hNX) W ->
  @current_support R h2 n Full hFull m T `<=` W ->
  (forall x,W x->@current_test_value R h2 n Full hFull m beta x=
    ev (KH (Inc (RawOmega omega))) x) ->
  @current_value R h2 n Full hFull (1+m)%N
    (@current_translation_chain R h2 n m z T) omega=
  @current_value R h2 n Full hFull m T beta.
Proof.
move=>hW hSupport hBeta.
pose betaRaw:=@current_test_equal_domain R h2 n m Full Full hFull hSource (erefl _) beta.
have hReplacement:@is_current_homotopy_test_replacement R h2 n n m m
    (fun _=>True) Full Full (fun x:X=>x) tau H hH
    (@current_translation_chain_input R h2 n m z T)
    (Inc (RawOmega omega)) betaRaw.
  exists W;split;first exact:hW.
  split.
  - by rewrite /current_translation_chain_input current_domain_transport_support.
  split;first by move=>x _.
  move=>x hx;rewrite /betaRaw current_test_equal_domain_values.
  exact:hBeta x hx.
rewrite /current_translation_chain current_equal_domain_test_action_reverse.
rewrite (@current_deformation_chain_test_action R h2 n n m
  (fun _=>True) Full Full (fun x:X=>x) tau H hH
  (@current_translation_chain_input R h2 n m z T)
  (@current_translation_chain_proper R h2 n m z T)
  (RawOmega omega) betaRaw hReplacement).
exact:(@current_equal_domain_test_action R h2 n m Full Full hFull hSource
  (erefl _) T beta).
Qed.
End CurrentTranslationChainTestAction.
