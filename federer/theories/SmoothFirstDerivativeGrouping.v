(** Federer (1969), 4.1.1, p. 346: control higher derivatives
    of the first derivative by the original higher derivatives.
    The proof reuses the exact isometric grouping theorem of
    3.1.11, p. 219, with its original derivative domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearGroupingFamily NormHigherDifferentialUP
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
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).
Local Notation W := (fun k=>@ContinuousMultilinear.space R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation evW := (fun k=>@ContinuousMultilinear.evaluation R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation WN := (fun k=>@ContinuousMultilinear.norm R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation hW := (fun k=>@ContinuousMultilinear.laws R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_first_derivative_grouping_exists]: actual
    D^j(Df) is isometrically the original D^(1+j)f, supporting
    continuity of test-function differentiation in Federer 4.1.1,
    p. 346. Existence follows from the already proved grouping
    laws; no new choice of a higher differential is assumed. *)
Theorem smooth_first_derivative_grouping_exists:
  exists J:forall j,Hom (Z (1+j)%N) (W j),
    (forall j z,@WN j (J j z)=@ZN (1+j)%N z) /\
    forall j f x,U x ->
      has_norm_higher_differential NX evW WN U (fun y=>@D 1%N y f) j x
        (J j (@D (1+j)%N x f)).
Proof.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=
  @continuous_multilinear_grouping_family_exists R 1%N X Y NX NY hNX hNY Z evZ ZN hZ W evW WN hW.
exists J; split; first exact hJN.
move=>j f x hx.
pose B y:=exists z,has_norm_higher_differential NX evZ ZN U (ev f) 1%N y z.
have hB:B=U.
  apply:funext=>y; apply:propext; split.
  - move=>[z hz]; exact:(@norm_higher_differential_domain R X Y NX hNX Z evZ ZN U (ev f) 1%N y z hz).
  - move=>hy; exists (@D 1%N y f).
    exact:(@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f y hy).
have hRep y z:has_norm_higher_differential NX evZ ZN U (ev f) 1%N y z -> @D 1%N y f=z.
  move=>hz; have hy:=@norm_higher_differential_domain R X Y NX hNX Z evZ ZN U (ev f) 1%N y z hz.
  exact:(norm_higher_differential_unique hNX hNY hZ
    (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f y hy) hz).
have hGroup:=@norm_higher_differential_grouping R X Y NX NY hNX Z evZ ZN hZ
  1%N W evW WN J K hJ hJN hJK hKJ U (ev f) (fun y=>@D 1%N y f) hRep
  j x (J j (@D (1+j)%N x f)).
have hh:has_norm_higher_differential NX evW WN B (fun y=>@D 1%N y f) j x
    (J j (@D (1+j)%N x f)).
  apply:hGroup.2; exists (@D (1+j)%N x f); split=>//.
  exact:(@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD (1+j)%N f x hx).
by rewrite hB in hh.
Qed.
End FirstDerivativeGrouping.
