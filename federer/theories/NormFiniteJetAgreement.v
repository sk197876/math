(** Federer (1969), 3.4.5, pp. 318–321: finite
    actual jets and analytic germ operations. This supporting
    comparison is the actual Taylor uniqueness corollary of
    3.1.11, p. 221, on the original domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP FiniteArgumentPermutation NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialSymmetry NormClassHigherUP NormClassHigherFields
  NormTaylorRemainderBound NormTaylorLineRemainder NormHigherDifferentialRadialIdentification NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Agreement.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y.
Variable NZ:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@NZ i).

(** Source for [norm_finite_jet_agreement]: agreement of
    all actual differentials through the specified finite order
    at the original centre, supporting 3.4.5, pp. 318–321.
    This is a predicate and chooses no representatives. *)
Definition norm_finite_jet_agreement (A B:X->Prop) (f g:X->Y) k a:=
  forall i,(i<=k)%N ->forall z:Z i,
    has_norm_higher_differential NX ev NZ A f i a z <->
    has_norm_higher_differential NX ev NZ B g i a z.

(** Source for [norm_radial_remainder_finite_jet_agreement]:
    an actual linewise negligible difference determines identical
    finite jets for two class-k functions, by actual
    Taylor coefficient uniqueness in 3.1.11, p. 221;
    supporting the local algebra of 3.4.5, pp. 318–321. *)
Theorem norm_radial_remainder_finite_jet_agreement (A B:X->Prop) (f g:X->Y) k a:
  A a ->B a ->
  norm_class_higher NX NY ev NZ A f k ->
  norm_class_higher NX NY ev NZ B g k ->
  (forall v,norm_little_o_power NY (fun t=>f (a+t*:v)-g (a+t*:v)) k) ->
  norm_finite_jet_agreement A B f g k a.
Proof.
move=>ha hb hf hg hRemainder.
have [G [hG hContinuous]]:=norm_class_higher_fields hNX hNY hZ hg.
pose D i:=G i a.
have hSymmetry i (hi:(i<=k)%N) s u:
    @ev i (finite_argument_permutation s u) (D i)=@ev i u (D i).
  exact:(@norm_higher_differential_symmetric R X Y NX NY hNX hNY Z ev NZ hZ B g i a
    (D i) (hG i hi a hb) s u).
have hApprox v:norm_little_o_power NY
    (fun t=>f (a+t*:v)-norm_taylor_value ev (fun i _=>D i) a (t*:v) k) k.
  have hTaylor:=@norm_taylor_line_little_o_fields R X Y NX NY hNX hNY Z ev NZ hZ B g G k a v
    hb hg.1 hG (hContinuous k (leqnn k)).
  have hSum:=norm_little_o_power_add hNY (hRemainder v) hTaylor.
  move=>e he;have [r [hr hBound]]:=hSum e he.
  exists r;split;first exact:hr.
  move=>t ht;have:=hBound t ht;by rewrite subrKA.
have hActual:=@norm_higher_differential_from_radial_expansion R X Y NX NY hNX hNY Z ev NZ hZ
  A f k a D ha hf hSymmetry hApprox.
move=>i hi z;split=>hz.
- have hEqual:z=D i:=norm_higher_differential_unique hNX hNY hZ hz (hActual i hi).
  rewrite hEqual;exact:(hG i hi a hb).
- have hEqual:z=D i:=norm_higher_differential_unique hNX hNY hZ hz (hG i hi a hb).
  rewrite hEqual;exact:(hActual i hi).
Qed.
End Agreement.
