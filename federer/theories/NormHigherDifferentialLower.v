(** Federer (1969), 3.1.11, pp. 219–221:
    existence of a kth differential supplies all
    lower differentials at the same point, as
    needed to define the kth jet. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormHigherDifferentialUP NormHigherDifferentialUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section LowerExistence.
Variable R : realType.
Variables X Y : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Variable A : X->Prop.
Variable f : X->Y.

(** Source for [norm_higher_differential_lower_exists]:
    the recursive definition on p. 219
    ensures that every coefficient used for
    the kth jet on Federer 3.1.11,
    p. 221, already exists. A
    class-k neighborhood hypothesis is unnecessary. *)
Theorem norm_higher_differential_lower_exists k j a :
  (j<=k)%N ->
  (exists z, has_norm_higher_differential NX ev ZN A f k a z) ->
  exists w, has_norm_higher_differential NX ev ZN A f j a w.
Proof.
elim:k j=>[j hj hz|k ih j hj [z hz]].
- have -> : j= 0%N by move:hj; rewrite leqn0=>/eqP.
  exact hz.
- case:(eqVneq j k.+1)=>[->|hne]; first by exists z.
  have hjk : (j<=k)%N by move:hj; rewrite leq_eqVlt (negbTE hne) /= ltnS.
  apply: ih hjk _.
  exact: (@norm_higher_differential_previous_domain R X Y NX hNX
    Z ev ZN A f k a z hz).
Qed.

(** Source for [norm_higher_differential_point_family_exists]:
    simultaneous actual coefficients through order k
    at one point, supporting the jet
    definition in Federer 3.1.11, p. 221.
    No claim is made for the arbitrary
    values selected above that order. *)
Theorem norm_higher_differential_point_family_exists k a (z : Z k) :
  has_norm_higher_differential NX ev ZN A f k a z ->
  exists D : forall i, Z i,
    forall i, (i<=k)%N -> has_norm_higher_differential NX ev ZN A f i a (D i).
Proof.
move=>hz.
have hex i : exists w : Z i,
    (i<=k)%N -> has_norm_higher_differential NX ev ZN A f i a w.
  case hi:(i<=k)%N.
  - have [w hw] := norm_higher_differential_lower_exists hi (ex_intro _ z hz).
    by exists w.
  - exists 0; by [].
pose D i := projT1 (cid (hex i)).
exists D=>i hi; exact: projT2 (cid (hex i)) hi.
Qed.
End LowerExistence.
