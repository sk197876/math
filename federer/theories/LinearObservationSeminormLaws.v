(** Federer (1969), 4.1.1, p. 343: the derivative suprema are
    seminorms. These consequences use their least-bound laws and
    linearity of the observations, without unfolding a supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP UniformFunctionNormUP UniformFunctionNormLaws
  LinearObservationSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LinearObservationLaws.
Variable R:realType.
Variable E:lmodType R.
Variable I:Type.
Variable W:I->lmodType R.
Variable N:forall i,W i->R.
Variable L:forall i,Hom E (W i).
Variable p:E->R.
Hypothesis hN:forall i,is_real_seminorm (@N i).
Hypothesis hp:is_linear_observation_seminorm N L p.

(** Source for [linear_observation_seminorm_bound]: every actual
    derivative norm is bounded by nu^i_K, supporting Federer
    4.1.1, p. 343. *)
Lemma linear_observation_seminorm_bound f i : @N i (@L i f)<=p f.
Proof.
have h:=uniform_function_norm_bound (hp f) i.
by rewrite (ger0_norm (real_seminorm_nonnegative (hN i) (@L i f))) in h.
Qed.

(** Source for [linear_observation_seminorm_least]: nu^i_K is
    the least nonnegative common derivative bound, supporting
    Federer 4.1.1, p. 343. *)
Lemma linear_observation_seminorm_least f C :
  0<=C -> (forall i,@N i (@L i f)<=C) -> p f<=C.
Proof.
move=>hC hB; apply:(@uniform_function_norm_least R I _ _ (hp f) C hC)=>i.
rewrite (ger0_norm (real_seminorm_nonnegative (hN i) (@L i f))); exact:hB.
Qed.

(** Source for [linear_observation_seminorm_is_seminorm]: the
    seminorm assertion for nu^i_K, Federer 4.1.1, p. 343. The
    proof retains an empty compact set and derivative order zero. *)
Theorem linear_observation_seminorm_is_seminorm : is_real_seminorm p.
Proof.
constructor.
- move=>f; exact:uniform_function_norm_nonnegative (hp f).
- move=>c f.
  have hs:=@uniform_function_norm_scale R I (fun i=>@N i (@L i f)) (p f) `|c| (hp f).
  rewrite normr_id in hs.
  have he:(fun i=>`|c| * @N i (@L i f))=(fun i=>@N i (@L i (c*:f))).
    apply:funext=>i; by rewrite linearZ (real_seminorm_scale (hN i)).
  rewrite he in hs; exact:uniform_function_norm_unique (hp (c*:f)) hs.
- move=>f g; apply:linear_observation_seminorm_least.
  + exact:addr_ge0 (uniform_function_norm_nonnegative (hp f))
      (uniform_function_norm_nonnegative (hp g)).
  + move=>i; rewrite linearD.
    exact:le_trans (real_seminorm_triangle (hN i) _ _)
      (lerD (linear_observation_seminorm_bound f i) (linear_observation_seminorm_bound g i)).
Qed.
End LinearObservationLaws.

(** Source for [linear_observation_seminorm_unique]: supporting
    uniqueness of the exact derivative supremum in Federer
    4.1.1, p. 343. *)
Theorem linear_observation_seminorm_unique (R:realType) (E:lmodType R)
    (I:Type) (W:I->lmodType R) (N:forall i,W i->R)
    (L:forall i,Hom E (W i)) (p q:E->R) :
  is_linear_observation_seminorm N L p ->
  is_linear_observation_seminorm N L q -> p = q.
Proof.
move=>hp hq; apply:funext=>f; exact:uniform_function_norm_unique (hp f) (hq f).
Qed.
