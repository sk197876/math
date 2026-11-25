(** Federer (1969), 3.1.11, p. 219:
    proved compatible isometric identifications for
    every final block size q, with a fixed
    first block of size p. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearGrouping
  MultilinearArguments NormLinearIsometryInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_grouping_family_exists]:
    all the grouping identifications used in the
    induction on q for Federer 3.1.11,
    p. 219, exist and preserve the
    corrected multilinear norm. Only their laws
    are exposed by this existence theorem. *)
Theorem continuous_multilinear_grouping_family_exists (R : realType) p
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (W : nat->lmodType R)
    (ew : forall q, {ffun 'I_q->X}->Hom (W q) (Z p))
    (WN : forall q, W q->R)
    (hW : forall q, is_continuous_multilinear_space NX (@ZN p) (@ew q) (@WN q)) :
  exists (J : forall q, Hom (Z (p+q)%N) (W q))
         (K : forall q, Hom (W q) (Z (p+q)%N)),
    (forall q z u v, @ez p u (@ew q v (J q z))=
      @ez (p+q)%N (multilinear_arguments_join u v) z) /\
    (forall q z, @WN q (J q z)=@ZN (p+q)%N z) /\
    (forall q w, J q (K q w)=w) /\
    (forall q z, K q (J q z)=z).
Proof.
pose Pair q := (Hom (Z (p+q)%N) (W q)*Hom (W q) (Z (p+q)%N))%type.
have hex q : exists jk : Pair q,
    (forall z u v, @ez p u (@ew q v (jk.1 z))=
      @ez (p+q)%N (multilinear_arguments_join u v) z) /\
    (forall z, @WN q (jk.1 z)=@ZN (p+q)%N z) /\
    (forall w, jk.1 (jk.2 w)=w) /\
    (forall z, jk.2 (jk.1 z)=z).
  have [J [hE [hN hsurj]]] := @continuous_multilinear_grouping_exists
    R p q X Y (Z p) (Z (p+q)%N) (W q) NX NY hNX
    (@ez p) (@ZN p) (@ez (p+q)%N) (@ZN (p+q)%N) (@ew q) (@WN q)
    (@hZ p) (@hZ (p+q)%N) (@hW q).
  have hPnorm := continuous_multilinear_norm_is_norm hNY (@hZ p).
  have [K [hKJ [hJK hKN]]] := norm_linear_isometry_inverse_exists
    (continuous_multilinear_norm_is_norm hNY (@hZ (p+q)%N))
    (continuous_multilinear_norm_is_norm hPnorm (@hW q)) hN hsurj.
  by exists (J,K); split=> //; split=> //; split.
pose pair q := sval (constructive_indefinite_description (hex q)).
pose J q := (pair q).1.
pose K q := (pair q).2.
have hp q := svalP (constructive_indefinite_description (hex q)).
exists J, K; split; first by move=> q; exact: (hp q).1.
split; first by move=> q; exact: (hp q).2.1.
split; first by move=> q; exact: (hp q).2.2.1.
by move=> q; exact: (hp q).2.2.2.
Qed.
