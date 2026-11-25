(** Federer (1969), 4.1.18, p. 374: the actual
    translations, their test pullbacks and their smooth
    pushforwards for arbitrary currents. Properness is proved
    on the original support; compact support of T is
    never assumed.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialLocal
  NormOpenDomainLaws NormDiffeomorphismUP NormTranslationDiffeomorphism
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanAdditiveGroup
  ExteriorGrading ExteriorPowers ExteriorMapScaling AlternatingForms AlternatingDual
  AlternatingPairing CurrentCoefficientNorms CurrentSpaces CurrentEvaluation CurrentProperSupport
  CurrentProperSupportRestriction FunctionalSupportRelativeClosed
  SmoothCompactSet SmoothCompactTranslate SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothGlobalTranslationUP SmoothGlobalTranslationSealed TestGlobalTranslation
  SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentPushforwardUP CurrentPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslations.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation value:=(@current_test_value R h2 n Full hFull m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation Id:=(hom_of_linear (@linear_id R X)).
Variable z:X.
Local Notation tau:=(@euclidean_translation R n z).
Local Notation image:=(fun (x:X) (_:True)=>Logic.I).

(** Source for [current_translation_smooth]: the original
    tau_z of 2.7.16 is smooth, as recalled
    in 4.1.18, p. 374. *)
Theorem current_translation_smooth:
  norm_class_all_orders hNX hNX Full tau.
Proof.
move=>k.
have hClass:=norm_diffeomorphism_inverse_class
  (@norm_translation_diffeomorphism R X NX hNX z k).
apply:(@norm_class_domain_agreement R X X NX NX hNX hNX Full
  (fun x:X=>x+z) tau k _ hClass)=>x _.
by rewrite /euclidean_translation addrC.
Qed.

(** Source for [current_translation_differential]: D tau_z=Id,
    supporting both the original averaging and the sharp
    mass bound of 4.1.18, pp. 374–375. *)
Theorem current_translation_differential x:
  has_norm_differential NX NX Full tau x Id.
Proof.
have hBound:norm_bounded_linear NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>v;change (is_true (NX v<=1*NX v));rewrite mul1r.
have hId:=@norm_differential_linear R X X NX NX hNX hNX Full x
  Id (hFull x Logic.I) hBound.
have hConst:=@norm_differential_constant R X X NX NX hNX hNX Full x z (hFull x Logic.I).
have hSum:=@norm_differential_add R X X NX NX hNX Full
  (fun y:X=>y) (fun _:X=>z) x Id 0 hId hConst.
rewrite addr0 in hSum.
apply:(@norm_differential_domain_agreement R X X NX NX hNX Full
  (fun y:X=>y+z) tau x Id _ hSum)=>y _.
by rewrite /euclidean_translation addrC.
Qed.

(** Source for [current_translation_proper]: the translation
    is proper on every original current support, as
    required for the first display of 4.1.18, p. 374.
    A translated target compact intersects a closed support
    in a compact set, even when T itself is not compact. *)
Theorem current_translation_proper (T:C):
  @is_current_proper_on_support R h2 n n m Full hFull Full T tau image.
Proof.
apply:(@current_proper_support_compact_loci R h2 n n Full hFull Full
  tau image m T).2=>K.
have [A [hClosed hSupport]]:=@functional_support_relative_closed R X (A_m X R^o m)
  NX hNX Full DT value (@current_value R h2 n Full hFull m T).
pose KShift:=@smooth_compact_translate R X NX hNX K z.
have hEqual:[set x|@current_support R h2 n Full hFull m T x /\
    smooth_compact_carrier K (tau x)]=smooth_compact_carrier KShift `&` A.
  apply:funext=>x;apply:propext;split.
  - move=>[hx hKx];split.
    + change (smooth_compact_carrier K (x+z)).
      by rewrite /euclidean_translation addrC in hKx.
    + have hAt:(Full `&` A) x by rewrite -hSupport;exact:hx.
      exact:hAt.2.
  - move=>[hKx hAx];split.
    + rewrite /current_support hSupport;exact:conj Logic.I hAx.
    + change (smooth_compact_carrier K (x+z)) in hKx.
      by rewrite /euclidean_translation addrC.
rewrite hEqual;exact:compact_closedI (smooth_compact_is_compact KShift) hClosed.
Qed.

(** Source for [current_translation_test]: the already
    specified actual global test translation, used in
    the averaging display of 4.1.18, p. 374. *)
Definition current_translation_test:Hom DT DT:=
  @test_global_translation R X (A_m X R^o m) NX NY hNX hNY E ev hE z
    (@SmoothGlobalTranslation.operator R X (A_m X R^o m) NX NY hNX hNY E ev hE z)
    (@SmoothGlobalTranslation.laws R X (A_m X R^o m) NX NY hNX hNY E ev hE z).

(** Source for [current_translation_test_values]: literal
    translated values omega(z+x), supporting the first
    integral in 4.1.18, p. 374. *)
Theorem current_translation_test_values (omega:DT) x:
  value (current_translation_test omega) x=value omega (tau x).
Proof.
change (ev (smooth_test_inclusion hE (current_translation_test omega)) x=value omega (tau x)).
rewrite /current_translation_test test_global_translation_inclusion
  SmoothGlobalTranslation.laws /euclidean_translation addrC.
by [].
Qed.

(** Source for [current_translation_pullback_values]: the actual
    smooth pullback under tau_z is the literal translated
    form, as used in 4.1.18, p. 374. *)
Theorem current_translation_pullback_values (omega:E) x:
  ev (@SmoothFormPullback.operator R h2 n n m Full Full hFull hFull
    tau image current_translation_smooth omega) x=ev omega (tau x).
Proof.
rewrite (@smooth_form_pullback_values R n n m Full Full E E ev ev tau _
  (@SmoothFormPullback.laws R h2 n n m Full Full hFull hFull
    tau image current_translation_smooth) omega x Id Logic.I
  (current_translation_differential x)).
apply:pairing_ext=>eta;rewrite A_m_dual_pairing.
have hId:=@exterior_power_map_ext R X X (hom_as_linear Id) (@linear_id R X)
  (fun v=>erefl v) m eta.
by rewrite hId exterior_power_map_identity.
Qed.

(** Source for [current_translation_pushforward]: the original
    smooth tau_z#T for every current T, with its
    proved support properness, in 4.1.18, p. 374. *)
Definition current_translation_pushforward (T:C):C:=
  @CurrentPushforward.value R h2 n n m Full Full hFull hFull
    T tau image current_translation_smooth (@current_translation_proper T).

(** Source for [current_translation_pushforward_action]: the original
    tau_z#T acts on the actual translated compact test,
    the scalar action used in 4.1.18, p. 374. *)
Theorem current_translation_pushforward_action (T:C) (omega:DT):
  @current_value R h2 n Full hFull m (current_translation_pushforward T) omega=
    @current_value R h2 n Full hFull m T (current_translation_test omega).
Proof.
apply:(@CurrentPushforward.laws R h2 n n m Full Full hFull hFull
  T tau image current_translation_smooth (@current_translation_proper T)
  omega (current_translation_test omega)).
exists Full;split;first exact:openT.
split;first by move=>x _.
split;first by move=>x _.
move=>x _;rewrite current_translation_test_values current_translation_pullback_values.
by [].
Qed.
End CurrentTranslations.
