(** Federer (1969), 4.1.18, p. 374: the
    endpoints of the actual original translation
    homotopy push forward to T and tau_z#T.
    All proof presentations of the same full
    Euclidean domains are aligned internally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport CurrentWholeSupportClosed CurrentProperSupport
  CurrentProperSupportRestriction CurrentPushforwardSealed CurrentPushforwardEqualDomain
  CurrentLipschitzPushforwardSmooth CurrentJoinSliceMapClass
  CurrentTranslationHomotopy CurrentTranslationChain CurrentTranslations EuclideanAdditiveGroup
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyGeometry CurrentHomotopySliceClass
  CurrentHomotopyEndpointProper SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationEndpointImages.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable T:@current_space R h2 n Full hFull m.

(** Source for [current_whole_identity_support_proper]:
    identity is proper on the original closed
    support of every current, supporting the
    initial endpoint of 4.1.18, p. 374. *)
Theorem current_whole_identity_support_proper:
  @is_current_proper_on_support R h2 n n m Full hFull Full T
    (fun x:X=>x) (fun _ _=>Logic.I).
Proof.
apply:(@current_proper_support_compact_loci R h2 n n Full hFull Full
  (fun x:X=>x) (fun _ _=>Logic.I) m T).2=>K.
have hSet:[set x|@current_support R h2 n Full hFull m T x /\
    smooth_compact_carrier K x]=smooth_compact_carrier K `&`
      @current_support R h2 n Full hFull m T.
  apply:funext=>x;apply:propext;split;by move=>[hx hy];split.
rewrite hSet.
exact:compact_closedI (smooth_compact_is_compact K)
  (@current_whole_support_closed R h2 n m hFull T).
Qed.

Variable z:X.
Local Notation tau:=(@euclidean_translation R n z).
Local Notation H:=(@current_translation_homotopy R n z).
Local Notation hH:=(@current_translation_homotopy_laws R n z).
Local Notation hSource:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation input:=(@current_translation_chain_input R h2 n m z T).
Local Notation proper:=(@current_translation_chain_proper R h2 n m z T).
Local Notation endpoints:=(@current_homotopy_endpoint_images R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation classes:=(@current_smooth_homotopy_endpoint_classes R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH).
Local Notation hpF:=(@current_homotopy_start_proper R h2 n n m
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1 input proper).
Local Notation hpG:=(@current_homotopy_end_proper R h2 n n m
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1 input proper).

(** Source for [current_translation_initial_image]: the
    original h_z(0,x)=x endpoint gives T,
    Federer 4.1.18, p. 374, for arbitrary T. *)
Theorem current_translation_initial_image:
  @current_domain_transport R h2 n Full hTarget Full (erefl _) hFull m
    (@CurrentPushforward.value R h2 n n m Full Full hSource hTarget input
      (fun x:X=>x) endpoints.1 classes.1 hpF)=T.
Proof.
rewrite (@current_pushforward_equal_domain R h2 n n m Full Full
  hFull hSource hFull hTarget (fun x:X=>x)
  (fun _ _=>Logic.I) endpoints.1 (@current_join_slice_identity_smooth R n)
  classes.1 T current_whole_identity_support_proper hpF).
exact:current_support_proper_identity_pushforward.
Qed.

(** Source for [current_translation_final_image]: the
    original h_z(1,x)=x+z endpoint gives the
    actual preceding translation pushforward,
    Federer 4.1.18, p. 374. *)
Theorem current_translation_final_image:
  @current_domain_transport R h2 n Full hTarget Full (erefl _) hFull m
    (@CurrentPushforward.value R h2 n n m Full Full hSource hTarget input
      tau endpoints.2 classes.2 hpG)=
    @current_translation_pushforward R h2 n m z T.
Proof.
exact:(@current_pushforward_equal_domain R h2 n n m Full Full
  hFull hSource hFull hTarget tau (fun _ _=>Logic.I) endpoints.2
  (@current_translation_smooth R n z) classes.2 T
  (@current_translation_proper R h2 n m z T) hpG).
Qed.
End CurrentTranslationEndpointImages.
