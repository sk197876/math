(** Federer (1969), 3.1.14, pp. 225–227: norm bounds for the
    higher differentials of a scalar function times a
    vector-valued function. The estimate on D^i g on p. 226
    applies the Leibniz formula of 3.1.11, p. 222, to a
    scalar factor. The scalar product is reduced to the
    bilinear Leibniz bound through a norming functional
    on the target; a trivial target is treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP SymmetricForms
  SymmetricOperatorNorm ContinuousMultilinearUP ContinuousMultilinearPostcompose
  NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialSymmetricForm NormHigherSymmetricFormUP
  NormHigherSymmetricFormFamilies NormClassHigherUP NormClassHigherLaws
  NormHigherDifferentialPostcompose NormClassHigherPostcompose
  NormHigherLeibnizBound SeminormNormingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ScalarLine.
Variable R : realType.
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.

(** Source for [scalar_line_linear]: the map t to t y_0 of
    the scalar line into the target, used to write the
    scalar factor in the D^i g estimate of Federer 3.1.14,
    p. 226, as a vector-valued function. Supporting lemma. *)
Lemma scalar_line_linear (y0 : Y) : linear (fun t : R^o=>t*:y0).
Proof.
by move=>c s t; change ((c*s+t)*:y0=c*:(s*:y0)+t*:y0); rewrite scalerDl scalerA.
Qed.

(** Source for [scalar_line_map]: the linear map t to t y_0,
    supporting the D^i g estimate of Federer 3.1.14,
    p. 226. Supporting definition. *)
Definition scalar_line_map (y0 : Y) : Hom R^o Y :=
  @HomMap R R^o Y (fun t : R^o=>t*:y0) (introT (asboolP _) (scalar_line_linear y0)).

(** Source for [scalar_line_mapE]: evaluation of the line map,
    Federer 3.1.14, p. 226. Supporting lemma. *)
Lemma scalar_line_mapE y0 t : scalar_line_map y0 t=t*:y0.
Proof. by []. Qed.

(** Source for [scalar_line_map_bounded]: the line map is bounded
    by the norm of y_0, as needed to apply the linear chain rule of
    Federer 3.1.11, p. 220, in 3.1.14, p. 226. Supporting lemma. *)
Lemma scalar_line_map_bounded y0 :
  norm_bounded_linear (fun t : R^o=>`|t|) NY (scalar_line_map y0).
Proof.
exists (NY y0); split; first exact: real_seminorm_nonnegative hNY.1 y0.
move=>t; rewrite scalar_line_mapE (real_seminorm_scale hNY.1) mulrC; exact: lexx.
Qed.

(** Source for [functional_scaling_bilinear]: the bilinear map
    (u,v) to omega(u) v, through which the scalar product of
    Federer 3.1.14, p. 226, becomes the bilinear product of
    3.1.11, p. 222. Supporting lemma. *)
Lemma functional_scaling_bilinear (omega : {linear Y->R^o}) :
  bilinear (fun u v : Y=>omega u*:v).
Proof.
split.
- move=>v c u w; rewrite /= linearP /= scalerDl scalerA.
  by change ((c*omega u)*:v+omega w*:v=(c*omega u)*:v+omega w*:v).
- by move=>u c v w; rewrite /= scalerDr !scalerA [omega u*c]mulrC.
Qed.

(** Source for [functional_scaling_bound]: a functional bounded by
    the norm gives a product bound for (u,v) to omega(u) v, as
    required by the Leibniz bound used in Federer 3.1.14,
    p. 226. Supporting lemma. *)
Lemma functional_scaling_bound (omega : {linear Y->R^o}) :
  (forall v, `|omega v|<=NY v) -> forall u v, NY (omega u*:v)<=NY u*NY v.
Proof.
move=>ho u v; rewrite (real_seminorm_scale hNY.1).
exact: (ler_wpM2r (real_seminorm_nonnegative hNY.1 v) (ho u)).
Qed.

(** Source for [norming_unit_functional]: a unit vector y_0 and a
    functional of norm at most one with omega(y_0)=1, obtained from
    the norming functional of Federer 2.4.12, p. 86, for the
    reduction in 3.1.14, p. 226. Supporting lemma. *)
Lemma norming_unit_functional (y : Y) : y!=0 ->
  exists (y0 : Y) (omega : {linear Y->R^o}),
    NY y0= 1 /\ omega y0= 1 /\ forall v, `|omega v|<=NY v.
Proof.
move=>hy.
have hpos : 0<NY y by rewrite (real_norm_positive hNY.1 hNY.2).
have hne : NY y!=0 by rewrite (gt_eqF hpos).
have hy0 : NY ((NY y)^-1*:y)= 1.
  by rewrite (real_seminorm_scale hNY.1) gtr0_norm ?invr_gt0 // mulVf.
have [omega [ho ho1]] := seminorm_norming_functional hNY.1 ((NY y)^-1*:y).
exists ((NY y)^-1*:y), omega; split; first exact hy0.
split; last exact ho.
by rewrite ho1.
Qed.

(** Source for [trivial_target_multilinear_norm_bound]: when the
    target has only the zero vector, every element of the
    multilinear space of Federer 3.1.11, p. 219, has norm
    below every nonnegative number. Supporting lemma for the
    degenerate case of the estimate in 3.1.14, p. 226. *)
Lemma trivial_target_multilinear_norm_bound (X Z : lmodType R) (NX : X->R)
    (hNX : is_real_seminorm NX) j
    (ev : {ffun 'I_j->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN) (z : Z) (C : R) :
  (forall v : Y, v=0) -> 0<=C -> ZN z<=C.
Proof.
move=>h0 hC.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ z) hC)=>u.
rewrite (h0 (ev u z)) (real_seminorm_zero hNY.1).
apply: mulr_ge0 hC _; apply: prodr_ge0=>l _; exact: real_seminorm_nonnegative hNX _.
Qed.

Section LinePostcompose.
Variable X : lmodType R.
Variable NX : X->R.
Variable j : nat.
Variables W Z : lmodType R.
Variable ew : {ffun 'I_j->X}->Hom W R^o.
Variable WN : W->R.
Hypothesis hW : is_continuous_multilinear_space NX (fun t : R^o=>`|t|) ew WN.
Variable ev : {ffun 'I_j->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space NX NY ev ZN.

(** Source for [scalar_line_postcompose_norm_bound]: composing a
    scalar multilinear map with the line map multiplies its norm
    of Federer 3.1.11, p. 219, by at most the norm of y_0.
    Supporting lemma for the derivative bounds of 3.1.14,
    p. 226. *)
Lemma scalar_line_postcompose_norm_bound (y0 : Y) (K : Hom W Z) (z : W) :
  (forall u, ev u (K z)=scalar_line_map y0 (ew u z)) ->
  ZN (K z)<=WN z*NY y0.
Proof.
move=>hK.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (K z))).
- exact: (mulr_ge0 (multilinear_operator_nonnegative
    (continuous_multilinear_norm_laws hW z)) (real_seminorm_nonnegative hNY.1 y0)).
- move=>u; rewrite hK scalar_line_mapE (real_seminorm_scale hNY.1) mulrAC.
  apply: (ler_wpM2r (real_seminorm_nonnegative hNY.1 y0)).
  exact: (multilinear_operator_bound (continuous_multilinear_norm_laws hW z) u).
Qed.
End LinePostcompose.
End ScalarLine.

(** Source for [norm_scalar_vector_higher_differential_bound]:
    the bound on D^i g for g=phi f with a scalar phi, used
    in Federer 3.1.14, p. 226, through the Leibniz formula
    of 3.1.11, p. 222: the ith differential of phi f at a is
    bounded by the sum over j of binomial(i,j) times the
    bounds on D^(i-j) phi and D^j f. The scalar factor is
    written as the composition of phi with the line map onto
    a unit vector, and the product as the bilinear map
    (u,v) to omega(u) v for a norming functional omega; a
    target with only the zero vector is treated directly.
    Supporting lemma for 3.1.14. *)
Theorem norm_scalar_vector_higher_differential_bound (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R) (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (W : nat->lmodType R) (ew : forall i, {ffun 'I_i->X}->Hom (W i) R^o)
    (WN : forall i, W i->R)
    (hW : forall i, is_continuous_multilinear_space NX (fun t : R^o=>`|t|) (@ew i) (@WN i))
    (A : X->Prop) (phi : X->R) (f : X->Y) k a
    (Dphi : forall i, W i) (Df : forall i, Z i) (F G : nat->R) i (z : Z i) :
  A a ->
  norm_class_higher NX (fun t : R^o=>`|t|) ew WN A phi k ->
  norm_class_higher NX NY ev ZN A f k ->
  (forall j, (j<=k)%N -> has_norm_higher_differential NX ew WN A phi j a (Dphi j)) ->
  (forall j, (j<=k)%N -> has_norm_higher_differential NX ev ZN A f j a (Df j)) ->
  (forall j, (j<=k)%N -> @WN j (Dphi j)<=F j) ->
  (forall j, (j<=k)%N -> @ZN j (Df j)<=G j) ->
  (i<=k)%N ->
  has_norm_higher_differential NX ev ZN A (fun x=>phi x*:f x) i a z ->
  @ZN i z<=\sum_(j<i.+1) ('C(i,j))%:R*(F (i-j)%N*G j).
Proof.
move=>ha hphi hf hDphi hDf hF hG hi hz.
have hNR := @scalar_absolute_value_norm R.
have hF0 j (hj : (j<=k)%N) : 0<=F j.
  exact: (le_trans (multilinear_operator_nonnegative
    (continuous_multilinear_norm_laws (hW j) (Dphi j))) (hF j hj)).
have hG0 j (hj : (j<=k)%N) : 0<=G j.
  exact: (le_trans (multilinear_operator_nonnegative
    (continuous_multilinear_norm_laws (hZ j) (Df j))) (hG j hj)).
have hsum0 : 0<=\sum_(j<i.+1) ('C(i,j))%:R*(F (i-j)%N*G j).
  apply: sumr_ge0=>j _.
  have hj : (j<=i)%N by move:(ltn_ord j); rewrite ltnS.
  apply: mulr_ge0 (ler0n _ _) _.
  exact: (mulr_ge0 (hF0 _ (leq_trans (leq_subr j i) hi)) (hG0 _ (leq_trans hj hi))).
have [[y hy]|hY] := pselect (exists y : Y, y!=0); last first.
  have h0 (v : Y) : v=0 by apply/eqP/negPn/negP=>hv; apply: hY; exists v.
  exact: (trivial_target_multilinear_norm_bound hNY hNX.1 (hZ i) z h0 hsum0).
have [y0 [omega [hy0 [ho1 homega]]]] := norming_unit_functional hNY hy.
have hMb := scalar_line_map_bounded hNY y0.
have [K [hK hKb]] := continuous_multilinear_postcompose_family_exists hW hZ hMb.
pose psi x := scalar_line_map y0 (phi x).
have hpsi : norm_class_higher NX NY ev ZN A psi k.
  exact: (norm_class_higher_postcompose hNX hNR hNY hW hZ hMb hphi).
have hDpsi j (hj : (j<=k)%N) :
    has_norm_higher_differential NX ev ZN A psi j a (K j (Dphi j)).
  have [_ [D [hD _]]] := norm_class_higher_lower hNX hNR hW hj hphi.
  have hpost := norm_higher_differential_field_postcompose
    hNX hNR hNY hW hZ hK hKb hD ha.
  by rewrite (norm_higher_differential_unique hNX hNR hW (hD a ha) (hDphi j hj)) in hpost.
have hKN j (hj : (j<=k)%N) : @ZN j (K j (Dphi j))<=F j.
  apply: (le_trans _ (hF j hj)).
  have hb := scalar_line_postcompose_norm_bound hNY (hW j) (hZ j) (hK j (Dphi j)).
  by rewrite hy0 mulr1 in hb.
have [Phi hPhi] := norm_higher_differential_point_forms hNX hNY hZ hDpsi.
have [Psi hPsi] := norm_higher_differential_point_forms hNX hNY hZ hDf.
pose mu (u v : Y) := omega u*:v.
have hmu : bilinear mu := functional_scaling_bilinear omega.
have hM : forall u v, NY (mu u v)<=NY u*NY v := functional_scaling_bound hNY homega.
have heq : (fun x=>phi x*:f x)=(fun x=>mu (psi x) (f x)).
  apply/funext=>x; rewrite /mu /psi scalar_line_mapE linearZ /= ho1.
  by change (phi x*:f x=(phi x*1)*:f x); rewrite mulr1.
have hz' : has_norm_higher_differential NX ev ZN A (fun x=>mu (psi x) (f x)) i a z.
  by rewrite -heq.
have [eta [heta hnorm]] := norm_higher_differential_symmetric_form_exists hNX hNY hZ hz'.
have hform : is_norm_higher_differential_form NX ev ZN A (fun x=>mu (psi x) (f x)) i a eta.
  exists z; split; first exact hz'.
  move=>u; rewrite heta; congr (@ev i _ z).
  by apply/ffunP=>j; rewrite ffunE tnth_mktuple.
have hopF j (hj : (j<=k)%N) : (symmetric_operator_norm hNX.1 NY (Phi j)<=(F j)%:E)%E.
  by rewrite (hPhi j hj).2 lee_fin; exact: hKN.
have hopG j (hj : (j<=k)%N) : (symmetric_operator_norm hNX.1 NY (Psi j)<=(G j)%:E)%E.
  by rewrite (hPsi j hj).2 lee_fin; exact: hG.
have hb := @norm_higher_leibniz_form_bound R X Y NX NY hNX hNY Z ev ZN hZ mu hmu hM
  A psi f k a Phi Psi F G i eta ha hpsi hf (fun j hj=>(hPhi j hj).1)
  (fun j hj=>(hPsi j hj).1) hopF hopG hi hform.
rewrite hnorm lee_fin in hb.
have -> : \sum_(j<i.+1) ('C(i,j))%:R*(F (i-j)%N*G j)=
    \sum_(j<i.+1) ('C(i,i-j))%:R*(F (i-j)%N*G j).
  apply: eq_bigr=>j _.
  have hj : (j<=i)%N by move:(ltn_ord j); rewrite ltnS.
  by rewrite (bin_sub hj).
exact hb.
Qed.
