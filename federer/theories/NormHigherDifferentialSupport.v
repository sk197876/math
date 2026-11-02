(** Federer (1969), 3.1.13, p. 224:
    all derivatives of the smooth bump vanish
    off its support. The supporting locality theorem
    uses the exact higher-differential graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_locally_zero]:
    a smooth function that is zero on
    an open neighbourhood has zero differentials
    there, supporting the compactly supported bump
    bounds in Federer 3.1.13, p. 224.
    The statement includes the zeroth differential. *)
Theorem norm_higher_differential_locally_zero (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (O : X->Prop) (f : X->Y) k a :
  (forall x, O x -> norm_domain_interior NX O x) ->
  (forall x, O x -> f x=0) -> O a ->
  has_norm_higher_differential NX ev ZN (fun _=>True) f k a 0.
Proof.
move=>hO hf ha.
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have he0 : @ev 0%N [ffun i : 'I_0=>(0:X)] 0=0 by rewrite linear0.
have hc0 : @constant_higher_form R Z 0 k=0 by case:k.
have hconst := @norm_higher_differential_constant R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) hopen 0 0 he0 k a I.
rewrite hc0 in hconst.
have hdom x (_ : O x) : (True<->True) by [].
have heq x (hx : O x) (_ : True) : f x=(fun _=>0) x := hf x hx.
exact: (@norm_higher_differential_local_agreement R X Y NX NY hNX hNY
  Z ev ZN hZ k (fun _=>True) (fun _=>True) O f (fun _=>0)
  hO hdom heq a ha 0).2 hconst.
Qed.
