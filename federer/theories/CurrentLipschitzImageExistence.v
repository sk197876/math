(** Federer (1969), 4.1.14, p. 371: the local
    image of an original locally flat current exists
    under properness only on its actual support.
    Local compact image actions agree for every
    admissible cutoff and are original currents on
    each fixed compact test family. The literal
    final topology gives the actual global current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentContraction
  SmoothTestSpaces SmoothTestEvaluation FlatCurrentsUP CurrentProperSupport
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentLipschitzPushforwardUP CurrentLipschitzCutoffExistence
  CurrentLipschitzCutoffIndependence CurrentLocalTestAction CurrentLocalFlatTestAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImageExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Local Notation D0:=(@current_test_space R h2 n U hU 0%N).
Local Notation DT:=(@current_test_space R h2 nu V hV m).
Local Notation CV:=(@current_space R h2 nu V hV m).
Local Notation contract:=(fun gamma:D0=>@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal).
Local Notation action:=(@current_value R h2 nu V hV m).
Local Notation Cutoff:=(@is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV T f).

(** Source for [current_lipschitz_image_exists]: the
    original locally flat image satisfies the literal
    equation for every admissible gamma, Federer
    4.1.14, p. 371. The selected testwise cutoffs
    are witnesses internal to the existence proof;
    they are absent from the independent specification. *)
Theorem current_lipschitz_image_exists:
  exists Q:CV,@is_current_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal T Q.
Proof.
have hCutoffExists (phi:DT):exists gamma:D0,Cutoff phi gamma.
  have[K hK]:=smooth_test_support_bound (@current_smooth_space_laws R h2 nu V hV m) phi.
  have[gamma hGamma]:=@current_lipschitz_compact_target_cutoff R h2 n nu m
    U V hU hV T f hImage hProper K.
  exists gamma;exact:hGamma phi hK.
have[gamma hGamma]:=choice hCutoffExists.
pose L:=fun phi:DT=>action (Push (contract (gamma phi)) (@hT (gamma phi))) phi.
have hLocalActions (K:smooth_compact_set hNY V):
    exists S:CV,@is_flat_current R h2 nu m V hV S /\
      forall phi:DT,@current_test_support R h2 nu m V hV phi `<=`
        smooth_compact_carrier K ->L phi=action S phi.
  have[delta hDelta]:=@current_lipschitz_compact_target_cutoff R h2 n nu m
    U V hU hV T f hImage hProper K.
  exists(Push (contract delta) (@hT delta));split.
  - exact:(@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
      f hImage hLocal (contract delta) (@hT delta)).1.
  - move=>phi hPhi.
    exact:(@current_lipschitz_cutoff_independent R h2 n nu m U V hU hV
      f hImage hLocal T hT phi (gamma phi) delta (hGamma phi) (hDelta phi hPhi)).
have hLocallyCurrent:@is_current_local_test_action R h2 nu m V hV L.
  move=>K;have[S [hFlat hS]]:=hLocalActions K;exists S;exact:hS.
have[Q hQ]:=@current_local_test_action_exists R h2 nu m V hV L hLocallyCurrent.
exists Q;split.
- apply:(@current_local_flat_test_agreement R h2 nu m V hV Q)=>K.
  have[S [hFlat hS]]:=hLocalActions K.
  exists S;split;first exact:hFlat.
  move=>phi hPhi;rewrite (hQ phi);exact:hS phi hPhi.
- move=>phi delta hFlatDelta hCutoff.
  rewrite (hQ phi).
  have hEquality:=@current_lipschitz_cutoff_independent R h2 n nu m U V hU hV
    f hImage hLocal T hT phi (gamma phi) delta (hGamma phi) hCutoff.
  have hProof:=@current_flat_lipschitz_pushforward_proof_independent R h2 n nu m
    U V hU hV f hImage hLocal (contract delta) (@hT delta) hFlatDelta.
  by rewrite hProof in hEquality.
Qed.
End CurrentLipschitzImageExistence.
