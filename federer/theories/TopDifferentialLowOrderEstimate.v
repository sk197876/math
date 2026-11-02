(** Federer (1969), 3.1.15, p. 228: the lower-order remainder estimate
    in the proof of the Whitney-type approximation. If f is of class
    k=p+q+1 on A, its kth differential field D^k f is differentiable at
    a with derivative L and remainder at most eta|x-a| on a ball, and
    the (k+1)st differential of f at a exists, then for i=p<=k-1 the
    pth differential of f and the pth differential of the (k+1)-jet
    P of f at a differ at b by at most eta|b-a|^(q+2)/(q+1)! along
    every segment from a to b inside A. The pth differential field
    G=D^p f is of class q+1 with (q+1)st differential D^k f under the
    canonical grouping isometry of 3.1.11, p. 219, and D^p P is the
    (q+2)-jet of G at a by 3.1.11, p. 221; the refined remainder
    estimate for G completes the argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness PolynomialFunctions
  MultilinearSuccessorArguments ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearSealed ContinuousMultilinearGroupingFamily
  NormDifferentialUP NormDifferentialLinear NormDifferentialFiniteCalculus
  NormLinearIsometryInverse NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialGrouping
  NormHigherDifferentialFields NormClassOneUP NormClassHigherUP NormClassHigherLaws
  NormClassHigherDerivative NormJetUP NormJetRestriction NormJetDifferentiation
  RefinedJetRemainder ContinuousMultilinearSuccessorLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LowOrder.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).

(** Source for [low_order_estimate]: Federer 3.1.15, p. 228, the
    estimate of D^i f(b)-D^i P_a(b) for i<=k-1, with i=p, k=p+q+1 and
    k+1-i=q+2. The field D^p f is of class q+1 on A by 3.1.11, p. 221,
    its (q+1)st differential is D^k f under the grouping isometry of
    3.1.11, p. 219, and D^p P_a is the (q+2)-jet of D^p f at a by
    3.1.11, p. 221; the refined remainder estimate then gives the
    bound eta|b-a|^(q+2)/(q+1)!. *)
Theorem low_order_estimate (p q K : nat) (hK : K=(p+q.+1)%N)
    (A : X->Prop) (f : X->Y) (hf : norm_class_higher NX NY ev ZN A f K)
    (Dk : X->Z K) (hDk : forall x, A x -> has_norm_higher_differential NX ev ZN A f K x (Dk x))
    (a : X) (L : Hom X (Z K)) (hL : has_norm_differential NX (@ZN K) A Dk a L)
    (zz : Z K.+1) (hzz : has_norm_higher_differential NX ev ZN A f K.+1 a zz)
    (hlift : forall u v, @ev K u (L v)=@ev K.+1 (multilinear_successor_arguments u v) zz)
    (eta r : R) (heta : 0<=eta) (hr : 0<r)
    (hrate : forall x, A x -> NX (x-a)<r -> @ZN K (Dk x-Dk a-L (x-a))<=eta*NX (x-a))
    (P : PolynomialFunction X Y) (hP : is_norm_jet_polynomial NX ev ZN A f K.+1 a P)
    (b : X) (hb : NX (b-a)<r) (hseg : forall t : R, 0<=t<= 1 -> A (a+t*:(b-a)))
    (w z : Z p) (hw : has_norm_higher_differential NX ev ZN (fun _=>True) P p b w)
    (hz : has_norm_higher_differential NX ev ZN A f p b z) :
  @ZN p (w-z)<=eta*(NX (b-a))^+q.+2/((q.+1)`!)%:R.
Proof.
subst K.
have hZNp : is_real_norm (@ZN p) := continuous_multilinear_norm_is_norm hNY (@hZ p).
pose W j := @ContinuousMultilinear.space R j X (Z p) NX (@ZN p) hNX hZNp.
pose ew j := @ContinuousMultilinear.evaluation R j X (Z p) NX (@ZN p) hNX hZNp.
pose WN j := @ContinuousMultilinear.norm R j X (Z p) NX (@ZN p) hNX hZNp.
have hW : forall j, is_continuous_multilinear_space NX (@ZN p) (@ew j) (@WN j).
  by move=> j; exact: (ContinuousMultilinear.laws j hNX hZNp).
have ha : A a.
  have h0 : 0<=(0:R)<= 1 by rewrite lexx ler01.
  by have := hseg 0 h0; rewrite scale0r addr0.
have hAint : forall x, A x -> norm_domain_interior NX A x.
  by move=> x hx; exact: (hf.1 x hx).1.
have hple : (p<=p+q.+1)%N := leq_addr _ _.
have [_ [G [hG hGc]]] := norm_class_higher_lower hNX hNY hZ hple hf.
have hGf : forall x, A x -> has_norm_higher_differential NX ev ZN A f p x (G x).
  by move=> x hx; exact: (hG x hx).
have hrep x v : has_norm_higher_differential NX ev ZN A f p x v -> G x=v.
  move=> hv; have hx := norm_higher_differential_domain hNX hv.
  exact (norm_higher_differential_unique hNX hNY hZ (hGf x hx) hv).
pose B x := exists v, has_norm_higher_differential NX ev ZN A f p x v.
have hAB : forall x, A x -> B x by move=> x hx; exists (G x); exact: (hGf x hx).
have [J [Kc [hJ [hJN [hJK hKJ]]]]] :=
  continuous_multilinear_grouping_family_exists hNX hNY hZ hW.
pose H' x := J q.+1 (Dk x).
have hH' : forall x, A x -> has_norm_higher_differential NX ew WN A G q.+1 x (H' x).
  move=> x hx.
  have hg := @norm_higher_differential_grouping R X Y NX NY hNX Z ev ZN hZ p W ew WN
    J Kc hJ hJN hJK hKJ A f G hrep q.+1 x (H' x).
  have hwB : has_norm_higher_differential NX ew WN B G q.+1 x (H' x).
    apply: hg.2; exists (Dk x); split=> //; exact: (hDk x hx).
  exact: (norm_higher_differential_open_restriction hNX hZNp hW G hAB hAint hx (H' x)).1 hwB.
have hGc1 : norm_class_higher NX (@ZN p) ew WN A G q.+1 :=
  norm_class_higher_derivative_field hNX hNY hZ hW hf hGf.
have hJb : norm_bounded_linear (@ZN (p+q.+1)%N) (@WN q.+1) (J q.+1) :=
  norm_linear_isometry_bounded (hJN q.+1).
pose L' := hom_comp (J q.+1) L.
have hL' : has_norm_differential NX (@WN q.+1) A H' a L' :=
  norm_differential_postcompose hNX hL hJb.
have hrate' : forall x, A x -> NX (x-a)<r ->
    @WN q.+1 (H' x-H' a-L' (x-a))<=eta*NX (x-a).
  move=> x hx hxr.
  have -> : H' x-H' a-L' (x-a)=J q.+1 (Dk x-Dk a-L (x-a)).
    by rewrite /H' /L' hom_compE !linearB.
  by rewrite hJN; exact: (hrate x hx hxr).
have hLb : norm_bounded_linear NX (@ZN (p+q.+1)%N) L := norm_differential_bounded hL.
have hL'b : norm_bounded_linear NX (@WN q.+1) L' := norm_bounded_linear_compose hLb hJb.
have [zz' hzz'lift] := continuous_multilinear_successor_lift_exists hNX hW hL'b.
have hzz' : has_norm_higher_differential NX ew WN A G q.+2 a zz' :=
  norm_higher_differential_field_step hNX hZNp hW hH' hL' hzz'lift.
have hP' : is_norm_jet_polynomial NX ev ZN A f (p+q.+2)%N a P by rewrite addnS.
have [Q [hDQ hQ]] := norm_jet_differentiation hNX hNY hZ hW hP' hrep.
have hQA : is_norm_jet_polynomial NX ew WN A G q.+2 a Q :=
  (norm_jet_open_restriction hNX hZNp hW G q.+2 Q hAB hAint ha).1 hQ.
have hmain := refined_jet_remainder hZNp hW hGc1 hH' hzz' hzz'lift heta hrate' hQA hb hseg.
have hab : a+(b-a)=b by rewrite addrC subrK.
rewrite hab in hmain.
have hwQ : w=Q b := norm_higher_differential_unique hNX hNY hZ hw (hDQ b).
have hzG : G b=z := hrep b z hz.
by rewrite hwQ -hzG (real_seminorm_subtract hZNp.1).
Qed.
End LowOrder.
