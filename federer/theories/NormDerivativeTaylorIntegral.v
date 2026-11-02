(** Federer (1969), 3.1.11, p. 221:
    Taylor integral remainders for D^p f.
    The coefficients are identified, by evaluation,
    with the grouped higher differentials of f. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormedStieltjesUP ContinuousMultilinearUP
  ContinuousMultilinearNorm MultilinearArguments NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialLocal
  NormHigherDifferentialIterated NormClassHigherUP NormClassHigherDerivative
  NormTaylorRemainderBound NormTaylorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_higher_differential_taylor_integral]:
    the displayed Taylor integral
    remainder for D^p f in Federer 3.1.11,
    p. 221. Evaluation of every coefficient
    recovers D^(p+i) f; thus the theorem
    does not assume a separate family of
    higher derivatives of the derivative field. *)
Theorem norm_higher_differential_taylor_integral (R : realType) p k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (W : nat->lmodType R)
    (ew : forall j, {ffun 'I_j->X}->Hom (W j) (Z p))
    (WN : forall j, W j->R)
    (hW : forall j, is_continuous_multilinear_space NX (@ZN p) (@ew j) (@WN j))
    (A : set X) (f : X->Y) (D : forall i, X->Z i) :
  norm_class_higher NX NY ez ZN A f (p+k.+1)%N ->
  (forall i, (i<=p+k.+1)%N -> forall a, A a ->
    has_norm_higher_differential NX ez ZN A f i a (D i a)) ->
  exists E : forall i, X->W i,
    (forall i, (i<=k.+1)%N -> forall a, A a ->
      has_norm_higher_differential NX ew WN A (D p) i a (E i a)) /\
    (forall i, (i<=k.+1)%N -> forall a, A a -> forall u v,
      @ez p u (@ew i v (E i a))=
        @ez (p+i)%N (multilinear_arguments_join u v) (D (p+i)%N a)) /\
    forall a v, (forall t : R, 0<=t<= 1 -> A (a+t*:v)) ->
      has_normed_stieltjes_integral (@ZN p)
        (fun t=>(((k.+1)`!)%:R)^-1*:
          (@ew k.+1 [ffun j : 'I_k.+1=>v] (E k.+1 a)-
           @ew k.+1 [ffun j : 'I_k.+1=>v] (E k.+1 (a+t*:v))))
        (fun t=>(1-t)^+k.+1) 0 1
        (D p (a+v)-\sum_(i<k.+2) ((i`!)%:R)^-1*:
          (@ew i [ffun j : 'I_i=>v] (E i a))).
Proof.
move=> hk hD.
have hple : (p<=p+k.+1)%N := leq_addr _ _.
have hDp := hD p hple.
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hc := norm_class_higher_derivative_field hNX hNY hZ hW hk hDp.
have [E [hE hrem]] := norm_class_higher_taylor_integral hNX hNp hW hc.
exists E; split; first exact hE.
split; last exact hrem.
move=> i hi a ha u v.
have hpi : (p+i<=p+k.+1)%N by rewrite leq_add2l.
have hrepresent x z :
    has_norm_higher_differential NX ez ZN A f p x z -> D p x=z.
  move=> hz; have hx := norm_higher_differential_domain hNX hz.
  exact (norm_higher_differential_unique hNX hNY hZ (hDp x hx) hz).
have [w [hw he]] := (@norm_higher_differential_iterated R p i
  X Y NX NY hNX hNY Z ez ZN hZ W ew WN hW A f (D p)
  a (D (p+i)%N a) hrepresent).1 (hD (p+i)%N hpi a ha).
pose B x := exists z, has_norm_higher_differential NX ez ZN A f p x z.
have hAB x : A x -> B x by move=> hx; exists (D p x); exact: hDp x hx.
have hopen x (hx : A x) := (hk.1 x hx).1.
have hr := @norm_higher_differential_open_restriction R X (Z p) NX (@ZN p)
  hNX hNp W ew WN hW i B A (D p) hAB hopen a ha w.
have hwA := hr.1 hw.
have hwe : w=E i a := norm_higher_differential_unique hNX hNp hW hwA (hE i hi a ha).
by rewrite -hwe; exact: he.
Qed.
