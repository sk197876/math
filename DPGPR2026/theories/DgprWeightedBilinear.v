(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, section 3, proof of lem:classes (cl:product):
    weighted bounds of the higher differentials of a bilinear expression
    B(f,g), obtained by induction on the order from the Leibniz formula
    D B(f,g) = B(Df,g) + B(f,Dg) of Federer 3.1.11, p. 220, and the
    isometric identification of D^q D f with D^(q+1) f of Federer 3.1.11,
    p. 219.

    The bounds are pointwise: a bound on D^(k) B(f,g)(x) uses only the
    bounds on D^i f(x) and D^i g(x), i <= k, at the same point x. Classes
    of weights closed under products and sums therefore propagate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  ContinuousMultilinearBilinearLift NormBoundedBilinearUP ContinuousMultilinearZero
  NormClassZeroBilinear NormHigherBilinearFirstField NormHigherDifferentialUP
  NormClassHigherUP NormClassHigherLaws NormClassHigherArithmetic
  NormClassHigherDerivative NormClassHigherBilinear
  NormHigherDifferentialGrouping ContinuousMultilinearGroupingFamily
  NormHigherDifferentialArithmetic NormHigherDifferentialUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section WeightedBilinear.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.
Variable A : X->Prop.
Variable K0 : X->Prop.

(** Source for [dgpr_weighted_derivative]: some weight w of the class C
    bounds ||D^i f(x)|| for x in K0, in the hierarchy (Z, ev, ZN) of
    continuous multilinear maps of Federer 3.1.11, p. 219; proof of
    lem:classes (cl:product). *)
Definition dgpr_weighted_derivative (Y : lmodType R) (Z : nat->lmodType R)
    (ev : forall j, {ffun 'I_j->X}->Hom (Z j) Y) (ZN : forall j, Z j->R)
    (C : (X->R)->Prop) (f : X->Y) (i : nat) :=
  exists w, C w /\ forall x z, K0 x -> has_norm_higher_differential NX ev ZN A f i x z ->
    ZN i z<=w x.

(** Source for [dgpr_first_differential_domain]: the domain of the first
    differential field of f is the domain A of f, Federer 3.1.11,
    p. 219; supporting lem:classes. *)
Lemma dgpr_first_differential_domain (Y : lmodType R) (Z : nat->lmodType R)
    (ev : forall j, {ffun 'I_j->X}->Hom (Z j) Y) (ZN : forall j, Z j->R)
    (f : X->Y) (F : X->Z 1%N) :
  (forall a, A a -> has_norm_higher_differential NX ev ZN A f 1 a (F a)) ->
  (fun x=>exists z, has_norm_higher_differential NX ev ZN A f 1 x z)=A.
Proof.
move=> hF; apply: funext=> x; apply: propext; split.
- by move=> [z hz]; exact: (norm_higher_differential_domain hNX hz).
- by move=> hx; exists (F x); exact: hF x hx.
Qed.

Variables C1 C2 C3 : (X->R)->Prop.
Hypothesis hC12 : forall b w1 w2, 0<=b -> C1 w1 -> C2 w2 ->
  exists w3, C3 w3 /\ forall x, K0 x -> b*(w1 x*w2 x)<=w3 x.
Hypothesis hC3 : forall w w', C3 w -> C3 w' ->
  exists w'', C3 w'' /\ forall x, K0 x -> w x+w' x<=w'' x.



(** Source for [dgpr_bilinear_weighted_derivative]: if f and g are of
    class k on A and their differentials of order at most k have weighted
    bounds in C1 and C2, then D^k B(f,g) has a weighted bound in C3,
    provided products of C1 and C2 weights are dominated by C3 weights and
    C3 is closed under sums. Leibniz formula, Federer 3.1.11, p. 220;
    proof of lem:classes (cl:product), blueprint section 3. *)
Theorem dgpr_bilinear_weighted_derivative k :
  forall (U V W : lmodType R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (P Q S : nat->lmodType R)
    (ep : forall j, {ffun 'I_j->X}->Hom (P j) U) (PN : forall j, P j->R)
    (eq : forall j, {ffun 'I_j->X}->Hom (Q j) V) (QN : forall j, Q j->R)
    (es : forall j, {ffun 'I_j->X}->Hom (S j) W) (SN : forall j, S j->R)
    (hP : forall j, is_continuous_multilinear_space NX NU (@ep j) (@PN j))
    (hQ : forall j, is_continuous_multilinear_space NX NV (@eq j) (@QN j))
    (hS : forall j, is_continuous_multilinear_space NX NW (@es j) (@SN j))
    (f : X->U) (g : X->V) (B : U->V->W),
  norm_bounded_bilinear NU NV NW B ->
  norm_class_higher NX NU ep PN A f k ->
  norm_class_higher NX NV eq QN A g k ->
  (forall i, (i<=k)%N -> dgpr_weighted_derivative ep PN C1 f i) ->
  (forall i, (i<=k)%N -> dgpr_weighted_derivative eq QN C2 g i) ->
  dgpr_weighted_derivative es SN C3 (fun x=>B (f x) (g x)) k.
Proof.
elim: k=>[|k ih] U V W NU NV NW hNU hNV hNW P Q S
  ep PN eq QN es SN hP hQ hS f g B hB hf hg hwf hwg.
- have [w1 [h1 hw1]] := hwf 0%N (leqnn 0).
  have [w2 [h2 hw2]] := hwg 0%N (leqnn 0).
  have [hbil [b [hb hbound]]] := hB.
  have [w3 [h3 hw3]] := hC12 hb h1 h2.
  exists w3; split=> // x z hSx [hx hz].
  have [p hp] := continuous_multilinear_zero_surjective hNU (hP 0%N) (f x).
  have [q hq] := continuous_multilinear_zero_surjective hNV (hQ 0%N) (g x).
  have hpn := hw1 x p hSx (conj hx hp).
  have hqn := hw2 x q hSx (conj hx hq).
  rewrite (continuous_multilinear_zero_norm hNW (hS 0%N)) hz.
  rewrite (continuous_multilinear_zero_norm hNU (hP 0%N)) hp in hpn.
  rewrite (continuous_multilinear_zero_norm hNV (hQ 0%N)) hq in hqn.
  apply: le_trans (hbound _ _) _.
  apply: le_trans (hw3 x hSx).
  exact: (ler_wpM2l hb (ler_pM (real_seminorm_nonnegative hNU.1 _)
    (real_seminorm_nonnegative hNV.1 _) hpn hqn)).
- have hfprev := norm_class_higher_previous hNX hNU hP hf.
  have hgprev := norm_class_higher_previous hNX hNV hQ hg.
  have h1 : (1<=k.+1)%N by [].
  have [_ [F [hF hcF]]] := @norm_class_higher_lower R X U NX NU
    hNX hNU P ep PN hP A f k.+1 1%N h1 hf.
  have [_ [G [hG hcG]]] := @norm_class_higher_lower R X V NX NV
    hNX hNV Q eq QN hQ A g k.+1 1%N h1 hg.
  have hPN := continuous_multilinear_norm_is_norm hNU (@hP 1%N).
  have hQN := continuous_multilinear_norm_is_norm hNV (@hQ 1%N).
  have hSN := continuous_multilinear_norm_is_norm hNW (@hS 1%N).
  pose PF j := @ContinuousMultilinear.space R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose epF j := @ContinuousMultilinear.evaluation R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose PNF j := @ContinuousMultilinear.norm R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  have hPF j : is_continuous_multilinear_space NX (@PN 1%N) (epF j) (PNF j).
    exact: ContinuousMultilinear.laws.
  pose QF j := @ContinuousMultilinear.space R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose eqF j := @ContinuousMultilinear.evaluation R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose QNF j := @ContinuousMultilinear.norm R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  have hQF j : is_continuous_multilinear_space NX (@QN 1%N) (eqF j) (QNF j).
    exact: ContinuousMultilinear.laws.
  pose SF j := @ContinuousMultilinear.space R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose esF j := @ContinuousMultilinear.evaluation R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose SNF j := @ContinuousMultilinear.norm R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  have hSF j : is_continuous_multilinear_space NX (@SN 1%N) (esF j) (SNF j).
    exact: ContinuousMultilinear.laws.
  have hf1k : norm_class_higher NX NU ep PN A f (1+k)%N by rewrite add1n.
  have hg1k : norm_class_higher NX NV eq QN A g (1+k)%N by rewrite add1n.
  have hFk := @norm_class_higher_derivative_field R 1%N k X U NX NU hNX hNU
    P ep PN hP PF epF PNF hPF A f F hf1k hF.
  have hGk := @norm_class_higher_derivative_field R 1%N k X V NX NV hNX hNV
    Q eq QN hQ QF eqF QNF hQF A g G hg1k hG.
  have [CF [hCF heF]] := @continuous_multilinear_bilinear_first_lift
    R 1%N X U V W (P 1%N) (S 1%N) NX NU NV NW hNV
    (@ep 1%N) (@PN 1%N) (@es 1%N) (@SN 1%N) (@hP 1%N) (@hS 1%N) B hB.
  have [CG [hCG heG]] := @continuous_multilinear_bilinear_second_lift
    R 1%N X U V W (Q 1%N) (S 1%N) NX NU NV NW hNU
    (@eq 1%N) (@QN 1%N) (@es 1%N) (@SN 1%N) (@hQ 1%N) (@hS 1%N) B hB.
  pose H x := CF (F x) (g x)+CG (f x) (G x).
  have hH := @norm_higher_first_bilinear_field R X U V W NX NU NV NW
    hNX hNU hNV hNW P Q S ep PN eq QN es SN hP hQ hS
    B CF CG A f g F G hB heF heG hF hG.
  (* derivative bounds of F and G through the grouping isometries *)
  have [JP [KP [hJP [hJPN [hJKP hKJP]]]]] :=
    continuous_multilinear_grouping_family_exists hNX hNU hP hPF.
  have [JQ [KQ [hJQ [hJQN [hJKQ hKJQ]]]]] :=
    continuous_multilinear_grouping_family_exists hNX hNV hQ hQF.
  have [JS [KS [hJS [hJSN [hJKS hKJS]]]]] :=
    continuous_multilinear_grouping_family_exists hNX hNW hS hSF.
  have hFrep x z : has_norm_higher_differential NX ep PN A f 1 x z -> F x=z.
    move=> hz; have hx := norm_higher_differential_domain hNX hz.
    exact: (norm_higher_differential_unique hNX hNU hP (hF x hx) hz).
  have hGrep x z : has_norm_higher_differential NX eq QN A g 1 x z -> G x=z.
    move=> hz; have hx := norm_higher_differential_domain hNX hz.
    exact: (norm_higher_differential_unique hNX hNV hQ (hG x hx) hz).
  have hHrep x z : has_norm_higher_differential NX es SN A (fun t=>B (f t) (g t)) 1 x z ->
      H x=z.
    move=> hz; have hx := norm_higher_differential_domain hNX hz.
    exact: (norm_higher_differential_unique hNX hNW hS (hH x hx) hz).
  have hdomF := dgpr_first_differential_domain hF.
  have hdomG := dgpr_first_differential_domain hG.
  have hdomH := dgpr_first_differential_domain hH.
  have hwF i : (i<=k)%N -> dgpr_weighted_derivative epF PNF C1 F i.
    move=> hi; have [w [hw hwb]] := hwf (1+i)%N hi.
    exists w; split=> // x y hSx hy.
    have hgr := @norm_higher_differential_grouping R X U NX NU hNX P ep PN hP
      1%N PF epF PNF JP KP hJP hJPN hJKP hKJP A f F hFrep i x y.
    rewrite hdomF in hgr.
    have [z [hz ->]] := hgr.1 hy.
    rewrite hJPN; exact: hwb x z hSx hz.
  have hwG i : (i<=k)%N -> dgpr_weighted_derivative eqF QNF C2 G i.
    move=> hi; have [w [hw hwb]] := hwg (1+i)%N hi.
    exists w; split=> // x y hSx hy.
    have hgr := @norm_higher_differential_grouping R X V NX NV hNX Q eq QN hQ
      1%N QF eqF QNF JQ KQ hJQ hJQN hJKQ hKJQ A g G hGrep i x y.
    rewrite hdomG in hgr.
    have [z [hz ->]] := hgr.1 hy.
    rewrite hJQN; exact: hwb x z hSx hz.
  have hwf' i : (i<=k)%N -> dgpr_weighted_derivative ep PN C1 f i.
    by move=> hi; apply: hwf; apply: leq_trans hi _.
  have hwg' i : (i<=k)%N -> dgpr_weighted_derivative eq QN C2 g i.
    by move=> hi; apply: hwg; apply: leq_trans hi _.
  have [w [hw hwb]] := ih (P 1%N) V (S 1%N) (@PN 1%N) NV (@SN 1%N)
    hPN hNV hSN PF Q SF epF PNF eq QN esF SNF hPF hQ hSF
    F g CF hCF hFk hgprev hwF hwg'.
  have [w' [hw' hw'b]] := ih U (Q 1%N) (S 1%N) NU (@QN 1%N) (@SN 1%N)
    hNU hQN hSN P QF SF ep PN eqF QNF esF SNF hP hQF hSF
    f G CG hCG hfprev hGk hwf' hwG.
  have [w'' [hw'' hle]] := hC3 hw hw'.
  have hFC := @norm_class_higher_bilinear R X NX hNX k (P 1%N) V (S 1%N)
    (@PN 1%N) NV (@SN 1%N) hPN hNV hSN PF Q SF epF PNF eq QN esF SNF hPF hQ hSF
    A F g CF hCF hFk hgprev.
  have hGC := @norm_class_higher_bilinear R X NX hNX k U (Q 1%N) (S 1%N)
    NU (@QN 1%N) (@SN 1%N) hNU hQN hSN P QF SF ep PN eqF QNF esF SNF hP hQF hSF
    A f G CG hCG hfprev hGk.
  have [_ [D1 [hD1 _]]] := hFC.
  have [_ [D2 [hD2 _]]] := hGC.
  have hsum := norm_higher_differential_field_add hNX hSN hSF hD1 hD2.
  exists w''; split=> // x z hSx hz.
  have hx := norm_higher_differential_domain hNX hz.
  have hgr := @norm_higher_differential_grouping R X W NX NW hNX S es SN hS
    1%N SF esF SNF JS KS hJS hJSN hJKS hKJS A (fun t=>B (f t) (g t)) H hHrep k x (JS k z).
  rewrite hdomH in hgr.
  have hJz : has_norm_higher_differential NX esF SNF A H k x (JS k z).
    by apply: hgr.2; exists z.
  have he := norm_higher_differential_unique hNX hSN hSF hJz (hsum x hx).
  have hz' : SN k.+1 z=SNF k (JS k z) by rewrite hJSN.
  rewrite hz' he.
  apply: le_trans (real_seminorm_triangle (continuous_multilinear_norm_is_norm hSN (hSF k)).1 _ _) _.
  apply: le_trans (hle x hSx).
  apply: lerD.
  - exact: hwb x _ hSx (hD1 x hx).
  - exact: hw'b x _ hSx (hD2 x hx).
Qed.
End WeightedBilinear.
