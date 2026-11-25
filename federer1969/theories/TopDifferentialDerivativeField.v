(** Federer (1969), 3.1.15, p. 227:
    the derivative D D^k f on the Lusin set, assembled from the
    approximate partial derivatives of the coordinates D^alpha f
    through the coordinate reconstruction of 3.1.11, p. 223. It is
    a bounded linear map at every point, varies continuously on the
    Lusin set, and agrees with the actual derivative of D^k f at
    every point of differentiability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology functions ring lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormDifferentialFiniteCalculus NormPartialDerivative
  NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  SymmetricMultiIndices NormHigherMultiPartialUP
  PartialFunctionUP PartialZeroExtension PartialContinuityUP
  EuclideanCoordinateHom TopDifferentialStepanoff TopDifferentialMeasurablePartials
  TopDifferentialLusinSelection CompactUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section DerivativeField.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation Yn := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable B : set X.
Variable f : X->R_n R n.
Variable Dk : X->Z k.
Hypothesis hDkf : forall x, B x -> has_norm_higher_differential N ev ZN B f k x (Dk x).
Local Notation P := (symmetric_indices m.+1 k*'I_m.+1)%type.
Variable iota : symmetric_indices m.+1 k->Hom (R_n R n) (Z k).
Hypothesis hiota_bound : forall alpha, norm_bounded_linear NY (@ZN k) (iota alpha).
Hypothesis hiota_rec : forall (A : X->Prop) (g : X->R_n R n) (a : X) (z : Z k),
  has_norm_higher_differential N ev ZN A g k a z ->
  z=\sum_alpha iota alpha (@ev k (norm_multi_partial_arguments R alpha) z).
Variable A2 : set X.
Variable E : set X.
Hypothesis hEA2 : E `<=` A2.
Hypothesis hEcont : forall p : P, partial_function_continuous_on E (top_partial_extension ev B Dk A2 p).
Variable val : P->X->Yn.
Hypothesis hval : forall (p : P) x, A2 x -> partial_function_graph (top_partial ev B Dk p.1 p.2) x (val p x).
Let hZNk : is_real_norm (@ZN k) := continuous_multilinear_norm_is_norm hNY (@hZ k).

(** Source for [hom_sum_eval]:
    evaluation of a finite sum of linear maps, Federer 1.1.? (linear
    algebra), supporting the assembly of D D^k f. *)
Lemma hom_sum_eval (U V : lmodType R) (I : finType) (F : I->Hom U V) (x : U) :
  (\sum_i F i) x=\sum_i F i x.
Proof.
elim/big_ind2: _=>[|a b c d ha hb|i _]; first exact: hom_zeroE.
- by rewrite hom_addE ha hb.
- by [].
Qed.

(** Source for [top_derivative]:
    D D^k f(a)=sum_alpha iota_alpha o (h |-> sum_i h_i ap D_i D^alpha f(a)),
    Federer 3.1.15, p. 227, with the coordinate reconstruction of 3.1.11. *)
Definition top_derivative (a : X) : Hom X (Z k) :=
  \sum_alpha hom_comp (iota alpha) ((@coordinate_hom R m.+1 (R_n R n) (fun i=>val (alpha,i) a))).

(** Source for [top_derivative_eval]:
    evaluation of the assembled derivative. *)
Lemma top_derivative_eval (a : X) (h : X) :
  top_derivative a h=\sum_alpha iota alpha ((@coordinate_hom R m.+1 (R_n R n) (fun i=>val (alpha,i) a)) h).
Proof. by rewrite /top_derivative hom_sum_eval; apply: eq_bigr=>alpha _; rewrite hom_compE. Qed.

(** Source for [top_derivative_bounded]:
    the assembled derivative is a bounded linear map, Federer 3.1.1, p. 209. *)
Lemma top_derivative_bounded (a : X) : norm_bounded_linear N (@ZN k) (top_derivative a).
Proof.
rewrite /top_derivative; elim/big_ind: _=>[|L M hL hM|alpha _].
- exact: (norm_bounded_linear_zero N hZNk).
- exact: (norm_bounded_linear_add hZNk hL hM).
- exact: (norm_bounded_linear_compose (coordinate_hom_bounded hNY _) (hiota_bound alpha)).
Qed.

(** Source for [top_derivative_constant]:
    the constant K=sum_alpha C_alpha sum_i |e_i| controlling the
    assembled derivative by the values of the partials. *)
Definition top_derivative_constant : R :=
  \sum_alpha (proj1_sig (cid (hiota_bound alpha)))*\sum_i N (@coordinate_basis R m.+1 i).

Lemma top_derivative_constant_nonnegative : 0<=top_derivative_constant.
Proof.
apply: sumr_ge0=>alpha _; apply: mulr_ge0.
- exact: (proj2_sig (cid (hiota_bound alpha))).1.
- apply: sumr_ge0=>i _; exact: (real_seminorm_nonnegative hN.1).
Qed.

(** Source for [top_derivative_difference_bound]:
    ||(D D^k f(b)-D D^k f(a)) h||<=|h| K max_p ||v_p(b)-v_p(a)||,
    supporting the continuity of D D^k f on the Lusin set,
    Federer 3.1.15, p. 227. *)
Lemma top_derivative_difference_bound (a b : X) (h : X) (delta : R) :
  (forall p : P, NY (val p b-val p a)<=delta) ->
  @ZN k ((top_derivative b-top_derivative a) h)<=top_derivative_constant*delta*N h.
Proof.
move=>hd.
have homB : forall (U V : lmodType R) (F G : Hom U V) x, (F-G) x=F x-G x.
  move=>U V F G x; rewrite -[-G]scaleN1r hom_addE hom_scaleE; by rewrite scaleN1r.
rewrite homB !top_derivative_eval -sumrB /top_derivative_constant !mulr_suml.
apply: (le_trans (real_seminorm_sum hZNk.1 _)); apply: ler_sum=>alpha _.
case: (cid (hiota_bound alpha))=>/= C [hC hCb].
have hcoord : forall v w : 'I_m.+1->R_n R n,
    coordinate_hom_fun v h-coordinate_hom_fun w h=coordinate_hom_fun (fun i=>v i-w i) h.
  by move=>v w; rewrite /coordinate_hom_fun -sumrB; apply: eq_bigr=>i _; rewrite scalerBr.
rewrite -raddfB hcoord.
apply: (le_trans (hCb _)).
rewrite -!mulrA; apply: (ler_wpM2l hC).
apply: (le_trans (coordinate_hom_bound hNY _ h)).
rewrite mulr_sumr mulr_suml; apply: ler_sum=>i _.
rewrite mulrCA [delta*N h]mulrC.
apply: (ler_wpM2l (real_seminorm_nonnegative hN.1 _)).
apply: (ler_wpM2l (real_seminorm_nonnegative hN.1 _)).
exact: (hd (alpha,i)).
Qed.

(** Source for [top_derivative_continuous]:
    D D^k f is continuous on the Lusin set E in the operator sense,
    Federer 3.1.15, p. 227 ("D D^k f|E is continuous"). *)
Theorem top_derivative_continuous (a : X) : E a -> forall e : R, 0<e ->
  exists d : R, 0<d /\ forall b, E b -> N (b-a)<d ->
    forall h, @ZN k ((top_derivative b-top_derivative a) h)<=e*N h.
Proof.
move=>ha e he.
set K := top_derivative_constant.
have hK : 0<=K := top_derivative_constant_nonnegative.
have hK1 : 0<K+1 by lra.
set e' := e/(K+1).
have he' : 0<e' by exact: divr_gt0.
have hon := @partial_function_zero_extension_on X Yn 0 A2.
have hdp : forall p : P, exists d : R, 0<d /\ forall b y', E b ->
    partial_function_graph (top_partial_extension ev B Dk A2 p) b y' ->
    mdist a b<d -> mdist (val p a) y'<e'.
  move=>p.
  have hga : partial_function_graph (top_partial_extension ev B Dk A2 p) a (val p a).
    exact: (hon (top_partial ev B Dk p.1 p.2) a (val p a) (hEA2 ha)).2 (hval p (hEA2 ha)).
  exact: (partial_continuity_pointwise (hEcont p) ha hga he').
have [dp hdp'] := choice hdp.
have [d [hd hdle]] := seq_positive_lower_bound (s:=index_enum P) (g:=dp)
  (fun p _=>(hdp' p).1).
exists d; split; first exact hd.
move=>b hb hba h.
have hvals : forall p : P, NY (val p b-val p a)<=e'.
  move=>p.
  have hgb : partial_function_graph (top_partial_extension ev B Dk A2 p) b (val p b).
    exact: (hon (top_partial ev B Dk p.1 p.2) b (val p b) (hEA2 hb)).2 (hval p (hEA2 hb)).
  have hab : mdist a b<dp p.
    rewrite inner_metric_distanceE; apply: (lt_le_trans _ (hdle p (mem_index_enum p))).
    by rewrite (real_seminorm_subtract hN.1).
  have hlt := (hdp' p).2 b (val p b) hb hgb hab.
  rewrite inner_metric_distanceE (real_seminorm_subtract hNY.1) in hlt.
  exact: ltW hlt.
apply: (le_trans (top_derivative_difference_bound h hvals)).
rewrite /e' -/K; apply: ler_wpM2r; first exact: (real_seminorm_nonnegative hN.1).
rewrite mulrCA -[e in X in _<=X]mulr1; apply: (ler_wpM2l (ltW he)).
by rewrite ler_pdivrMr // mul1r lerDl ler01.
Qed.

(** Source for [top_derivative_differential]:
    at a point of A2 where D^k f is differentiable within the
    domain, the assembled derivative is the actual derivative:
    the partials are the values of the derivative on the standard
    vectors, the coordinate combination recovers the derivative on
    every coordinate, and the reconstruction identity for actual
    differentials passes to the limit of difference quotients,
    Federer 3.1.15, p. 227, with 3.1.1, p. 211, and 3.1.11, p. 223. *)
Theorem top_derivative_differential (a : X) (L : Hom X (Z k)) : A2 a ->
  has_norm_differential N (@ZN k) B Dk a L -> top_derivative a=L.
Proof.
move=>ha hL.
have hevZ : forall (U V : lmodType R) (F : Hom U V) (c : R) z, F (c*:z)=c*:F z.
  by move=>U V F c z; have := hom_linear F c z 0; rewrite addr0 raddf0 addr0.
have hevS : forall (U V : lmodType R) (F : Hom U V) (I : finType) (G : I->U),
    F (\sum_i G i)=\sum_i F (G i).
  move=>U V F I G; elim/big_ind2: _=>[|x1 x2 y1 y2 hx hy|i _]; first exact: raddf0.
  - by rewrite -hx -hy; exact: raddfD.
  - by [].
have hvalL : forall (alpha : symmetric_indices m.+1 k) (i : 'I_m.+1),
    val (alpha,i) a=@ev k (norm_multi_partial_arguments R alpha) (L (@coordinate_basis R m.+1 i)).
  move=>alpha i.
  have hbnd : norm_bounded_linear (@ZN k) NY (@ev k (norm_multi_partial_arguments R alpha)).
    exists (\prod_(j<k) N (norm_multi_partial_arguments R alpha j)); split.
    - apply: prodr_ge0=>j _; exact: (real_seminorm_nonnegative hN.1).
    - move=>z; rewrite mulrC.
      exact: (multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ k) z) _).
  have hLa := norm_differential_postcompose hN hL hbnd.
  have hgr := top_partial_at_differentiability_point hLa i.
  rewrite hom_compE in hgr.
  exact: (partial_function_single_valued (hval (alpha,i) ha) hgr).
have hexp : forall h, L h=\sum_i h i*:L (@coordinate_basis R m.+1 i).
  move=>h.
  exact: (norm_differential_partial_expansion hN hZNk hL
    (fun i=>norm_differential_partial hN hZNk hL i) h).
pose Pi (z : Z k) : Z k := \sum_alpha iota alpha (@ev k (norm_multi_partial_arguments R alpha) z).
have hPiD : forall x, B x -> Pi (Dk x)=Dk x by move=>x hx; exact: esym (hiota_rec (hDkf hx)).
have hPiZ : forall (c : R) z, Pi (c*:z)=c*:Pi z.
  move=>c z; rewrite /Pi scaler_sumr; apply: eq_bigr=>alpha _; by rewrite !hevZ.
have hPiB : forall z w, Pi (z-w)=Pi z-Pi w.
  move=>z w; rewrite /Pi -sumrB; apply: eq_bigr=>alpha _; by rewrite !raddfB.
have hPibound : exists C : R, 0<=C /\ forall z, @ZN k (Pi z)<=C*@ZN k z.
  exists (\sum_alpha (proj1_sig (cid (hiota_bound alpha)))*
    \prod_(j<k) N (norm_multi_partial_arguments R alpha j)); split.
  - apply: sumr_ge0=>alpha _; apply: mulr_ge0; first exact: (proj2_sig (cid (hiota_bound alpha))).1.
    apply: prodr_ge0=>j _; exact: (real_seminorm_nonnegative hN.1).
  - move=>z; rewrite /Pi mulr_suml.
    apply: (le_trans (real_seminorm_sum hZNk.1 _)); apply: ler_sum=>alpha _.
    case: (cid (hiota_bound alpha))=>/= C [hC hCb].
    apply: (le_trans (hCb _)); rewrite -mulrA; apply: (ler_wpM2l hC).
    rewrite mulrC.
    exact: (multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ k) z) _).
apply: hom_ext=>h.
rewrite top_derivative_eval.
have -> : \sum_alpha iota alpha ((@coordinate_hom R m.+1 (R_n R n) (fun i=>val (alpha,i) a)) h)=Pi (L h).
  rewrite /Pi; apply: eq_bigr=>alpha _; congr (iota alpha _).
  rewrite /coordinate_hom_fun hexp hevS; apply: eq_bigr=>i _.
  by rewrite hevZ hvalL.
case: (pselect (h=0))=>[->|hh0].
  by rewrite raddf0 /Pi; apply: big1=>alpha _; rewrite !raddf0.
have hNh : 0<N h by rewrite (real_norm_positive hN.1 hN.2); apply/eqP.
have [C [hC hCb]] := hPibound.
have hC1 : 0<1+C by lra.
have hsmall : forall e : R, 0<e -> @ZN k (L h-Pi (L h))<=e.
  move=>e he.
  have hden : 0<(1+C)*N h by exact: mulr_gt0.
  have he' : 0<e/((1+C)*N h) by exact: divr_gt0.
  have [d [hd hrem]] := norm_differential_remainder hL he'.
  have [r [hr hball]] := norm_differential_interior hL.
  set t := Num.min (d/(2*N h)) (r/(2*N h)).
  have h2N : 0<2*N h by apply: mulr_gt0=>//; rewrite ltr0n.
  have ht : 0<t by rewrite lt_min; apply/andP; split; exact: divr_gt0.
  have hth : N (t*:h)=t*N h by rewrite (real_seminorm_scale hN.1) (gtr0_norm ht).
  have htd : N (t*:h)<d.
    rewrite hth; have : t<=d/(2*N h) by rewrite ge_min lexx.
    move=>hle; apply: (le_lt_trans (ler_wpM2r (ltW hNh) hle)).
    rewrite invfM -!mulrA mulVf ?mulr1; last exact: lt0r_neq0.
    lra.
  have htr : N (t*:h)<r.
    rewrite hth; have : t<=r/(2*N h) by rewrite ge_min lexx orbT.
    move=>hle; apply: (le_lt_trans (ler_wpM2r (ltW hNh) hle)).
    rewrite invfM -!mulrA mulVf ?mulr1; last exact: lt0r_neq0.
    lra.
  have hx : B (a+t*:h) := hball _ htr.
  have hq := hrem (t*:h) hx htd.
  set q := t^-1*:(Dk (a+t*:h)-Dk a).
  have hqL : @ZN k (q-L h)<=e/(1+C).
    have -> : q-L h=t^-1*:(Dk (a+t*:h)-Dk a-L (t*:h)).
      by rewrite /q hevZ [in RHS]scalerBr scalerA mulVf ?scale1r //; exact: lt0r_neq0.
    have hti : 0<t^-1 by rewrite invr_gt0.
    rewrite (real_seminorm_scale hZNk.1) (gtr0_norm hti).
    apply: (le_trans (ler_wpM2l (ltW hti) hq)).
    rewrite hth.
    have -> : t^-1*(e/((1+C)*N h)*(t*N h))=e/((1+C)*N h)*N h*(t^-1*t) by ring.
    rewrite mulVf ?mulr1; last exact: lt0r_neq0.
    rewrite invfM -!mulrA [(N h)^-1*N h]mulVf ?mulr1; last exact: lt0r_neq0.
    exact: lexx.
  have hBa : B a := norm_domain_interior_member hN (norm_differential_interior hL).
  have hPiq : Pi q=q by rewrite /q hPiZ hPiB (hPiD _ hx) (hPiD _ hBa).
  have hdecomp : L h-Pi (L h)=(L h-q)+Pi (q-L h) by rewrite hPiB hPiq addrA subrK.
  rewrite hdecomp.
  apply: (le_trans (real_seminorm_triangle hZNk.1 _ _)).
  have h1 : @ZN k (L h-q)<=e/(1+C) by rewrite (real_seminorm_subtract hZNk.1); exact hqL.
  have h2 : @ZN k (Pi (q-L h))<=C*(e/(1+C)) := le_trans (hCb _) (ler_wpM2l hC hqL).
  have hsum : e/(1+C)+C*(e/(1+C))=e.
    rewrite -{1}[e/(1+C)]mul1r -mulrDl mulrC -mulrA mulVf ?mulr1 //; exact: lt0r_neq0.
  by rewrite -hsum; exact: (lerD h1 h2).
have hz : @ZN k (L h-Pi (L h))=0.
  apply/eqP; rewrite eq_le (real_seminorm_nonnegative hZNk.1) andbT.
  by apply/ler_addgt0Pr=>e he; rewrite add0r; exact: hsmall.
by rewrite -(subr0_eq (hZNk.2 _ hz)).
Qed.
End DerivativeField.
