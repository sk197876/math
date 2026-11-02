(** Federer (1969), 3.1.13, p. 225:
    a prescribed finite family valid on a
    neighbourhood computes the actual differential of
    the locally finite sum. This permits the
    exact overlap count 129^m in the norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialLocal NormHigherDifferentialFiniteSums
  FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section LocalFiniteDifferentials.
Variable R : realType.
Variables X Y : lmodType R.
Variable J : choiceType.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variables (U O : X->Prop) (I : J->Prop).
Variables (f : J->X->Y) (g : X->Y).
Variable F : {fset J}.
Variable k : nat.
Variable D : J->X->Z k.
Hypothesis hsum : is_finite_family_sum_on U I f g.
Hypothesis hFI : forall j, j \in F -> I j.
Hypothesis hOU : forall x, O x -> U x.
Hypothesis hopen : forall x, O x -> norm_domain_interior NX O x.
Hypothesis hF : forall x, O x -> forall j, I j -> j \notin F -> f j x=0.
Hypothesis hD : forall j, I j -> forall x,
  has_norm_higher_differential NX ev ZN (fun _=>True) (f j) k x (D j x).

(** Source for [norm_local_finite_sum_differential]:
    the locally finite derivative sum in
    Federer 3.1.13, p. 225.
    The finite set must capture all active
    summands on a neighbourhood, rather than
    only at the single evaluation point. *)
Theorem norm_local_finite_sum_differential a :
  O a ->
  has_norm_higher_differential NX ev ZN U g k a (\sum_(j<-F) D j a).
Proof.
move=>ha.
have htop x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hfinite := @norm_higher_differential_finite_sum R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) htop F (fun j=>f (val j)) k
  (fun j=>D (val j)) (fun j x _=>hD (hFI (valP j)) x) a Logic.I.
pose p x := \sum_(j : F) f (val j) x.
have hdom x (hx : O x) : (True<->U x).
  split=>_; [exact: hOU x hx|exact Logic.I].
have he x (hx : O x) (_ : True) : p x=g x.
  rewrite (hsum (hOU hx) hFI (hF hx)) /p big_seq_fsetE; by [].
have hl := (@norm_higher_differential_local_agreement R X Y NX NY hNX hNY
  Z ev ZN hZ k (fun _=>True) U O p g hopen hdom he a ha
  (\sum_(j : F) D (val j) a)).1 hfinite.
by rewrite big_seq_fsetE.
Qed.

(** Source for [norm_local_finite_sum_differential_bound]:
    bounding each local summand by M
    gives the cardinality-times-M estimate used
    with the overlap bound in Federer
    3.1.13, p. 225. The
    theorem applies to the actual derivative
    value of the sum, by uniqueness. *)
Theorem norm_local_finite_sum_differential_bound a (z : Z k) M :
  O a ->
  has_norm_higher_differential NX ev ZN U g k a z ->
  (forall j, j \in F -> @ZN k (D j a)<=M) ->
  @ZN k z<=(#|` F|)%:R*M.
Proof.
move=>ha hz hb.
have he := norm_higher_differential_unique hNX hNY hZ
  (norm_local_finite_sum_differential ha) hz.
rewrite -he big_seq_fsetE.
have hNk := continuous_multilinear_norm_is_norm hNY (@hZ k).
apply: (le_trans (real_seminorm_sum hNk.1 _)).
have hs : (\sum_(j : F) @ZN k (D (val j) a))<=\sum_(j : F) M.
  apply: ler_sum=>j _; exact: (hb (val j) (valP j)).
by rewrite sumr_const -cardfE -mulr_natl in hs.
Qed.
End LocalFiniteDifferentials.
