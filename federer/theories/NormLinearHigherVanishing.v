(** Federer (1969), 3.1.24, pp. 239–240: the identity in the
    composition of inverse maps has zero differentials above order one.
    This is the degree-one polynomial case of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousOperatorUP
  NormHigherDifferentialUP NormHigherDifferentialFirst NormHigherDifferentialFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section LinearHigher.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable A:X->Prop.
Hypothesis hA:forall x,A x -> norm_domain_interior NX A x.

(** Source for [norm_higher_constant_field_step]: differentiating a
    constant actual differential field gives the zero next differential,
    supporting Federer 3.1.24, pp. 239–240. *)
Lemma norm_higher_constant_field_step (f:X->Y) k (z:Z k) :
  (forall x,A x -> has_norm_higher_differential NX ev ZN A f k x z) ->
  forall x,A x -> has_norm_higher_differential NX ev ZN A f k.+1 x 0.
Proof.
move=>hz x hx.
apply:(@norm_higher_differential_field_step R X Y NX NY hNX hNY Z ev ZN hZ A f k
  (fun _=>z) x 0 0 hz).
- exact (@norm_differential_constant R X (Z k) NX (@ZN k) hNX
    (continuous_multilinear_norm_is_norm hNY (hZ k)) A x z (@hA x hx)).
- by move=>u v; rewrite hom_zeroE !linear0.
Qed.

(** Source for [norm_linear_higher_vanishing]: a bounded linear map
    has zero actual differentials in every order at least two, the
    identity-map instance used in Federer 3.1.24, pp. 239–240.
    The abstract continuous multilinear spaces and any open domain suffice. *)
Theorem norm_linear_higher_vanishing (L:Hom X Y) :
  norm_bounded_linear NX NY L -> forall p,(2<=p)%N ->
  forall x,A x -> has_norm_higher_differential NX ev ZN A L p x 0.
Proof.
move=>hL.
have [z hz]:=continuous_operator_surjective
  (continuous_multilinear_one_operator_space (hZ 1%N)) hL.
have hFirst x (hx:A x):has_norm_higher_differential NX ev ZN A L 1%N x z.
  apply:(proj2 (@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A L x z)).
  change (has_norm_differential NX NY A L x (continuous_multilinear_one_evaluation (hZ 1%N) z)).
  rewrite hz; exact (@norm_differential_linear R X Y NX NY hNX hNY A x L (@hA x hx) hL).
have hTwo:=@norm_higher_constant_field_step L 1%N z hFirst.
have hAll n:forall x,A x -> has_norm_higher_differential NX ev ZN A L n.+2 x 0.
  elim:n=>[|n ih]; first exact hTwo.
  exact (@norm_higher_constant_field_step L n.+2 0 ih).
move=>[|[|p]] hp x hx; first by [].
- by [].
- exact (hAll p x hx).
Qed.
End LinearHigher.
