(** Federer (1969), 4.1.1, p. 346: control higher derivatives
    of the pth derivative by the original higher derivatives.
    The proof reuses the exact isometric grouping theorem of
    3.1.11, p. 219, with its original derivative domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm MultilinearArguments ContinuousMultilinearGroupingFamily NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialGrouping SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section FirstDerivativeGrouping.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable p:nat.
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ p)).
Local Notation W := (fun k=>@ContinuousMultilinear.space R k X (Z p) NX (@ZN p) hNX hN1).
Local Notation evW := (fun k=>@ContinuousMultilinear.evaluation R k X (Z p) NX (@ZN p) hNX hN1).
Local Notation WN := (fun k=>@ContinuousMultilinear.norm R k X (Z p) NX (@ZN p) hNX hN1).
Local Notation hW := (fun k=>@ContinuousMultilinear.laws R k X (Z p) NX (@ZN p) hNX hN1).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_higher_derivative_grouping_exists]: actual
    D^j(D^p f) is isometrically the original D^(p+j)f, supporting
    continuity of test-function differentiation in Federer 4.1.1,
    p. 346. Existence follows from the already proved grouping
    laws; no new choice of a higher differential is assumed. *)
Theorem smooth_higher_derivative_grouping_exists:
  exists J:forall j,Hom (Z (p+j)%N) (W j),
    (forall j z u v,@evZ p u (@evW j v (J j z))=
      @evZ (p+j)%N (multilinear_arguments_join u v) z) /\
    (forall j z,@WN j (J j z)=@ZN (p+j)%N z) /\
    forall j f x,U x ->
      has_norm_higher_differential NX evW WN U (fun y=>@D p y f) j x
        (J j (@D (p+j)%N x f)).
Proof.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=
  @continuous_multilinear_grouping_family_exists R p X Y NX NY hNX hNY Z evZ ZN hZ W evW WN hW.
exists J; split; first exact hJ; split; first exact hJN.
move=>j f x hx.
pose B y:=exists z,has_norm_higher_differential NX evZ ZN U (ev f) p y z.
have hB:B=U.
  apply:funext=>y; apply:propext; split.
  - move=>[z hz]; exact:(@norm_higher_differential_domain R X Y NX hNX Z evZ ZN U (ev f) p y z hz).
  - move=>hy; exists (@D p y f).
    exact:(@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD p f y hy).
have hRep y z:has_norm_higher_differential NX evZ ZN U (ev f) p y z -> @D p y f=z.
  move=>hz; have hy:=@norm_higher_differential_domain R X Y NX hNX Z evZ ZN U (ev f) p y z hz.
  exact:(norm_higher_differential_unique hNX hNY hZ
    (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD p f y hy) hz).
have hGroup:=@norm_higher_differential_grouping R X Y NX NY hNX Z evZ ZN hZ
  p W evW WN J K hJ hJN hJK hKJ U (ev f) (fun y=>@D p y f) hRep
  j x (J j (@D (p+j)%N x f)).
have hh:has_norm_higher_differential NX evW WN B (fun y=>@D p y f) j x
    (J j (@D (p+j)%N x f)).
  apply:hGroup.2; exists (@D (p+j)%N x f); split=>//.
  exact:(@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD (p+j)%N f x hx).
by rewrite hB in hh.
Qed.
End FirstDerivativeGrouping.
