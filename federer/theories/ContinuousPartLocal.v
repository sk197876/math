(** The bounded Borel-set argument of Federer (1969), 2.9.2, p. 153. First
    cancel finite complementary measures for Borel subsets; then use
    simultaneous phi/psi hulls for an arbitrary subset. The finiteness
    hypotheses used in cancellation and in the hull criterion are explicit.
    Source context: MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartMeasure
  ContinuousPartBorel ContinuousPartRestrictedAttainment ContinuousPartHulls CommonBorelHulls
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureHull BorelRegularMeasureUP
  TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_local_borel_restriction]: the first case of
    the local identity in Federer 2.9.2, p. 153, when S is a Borel subset of
    A. Two component inequalities and equality of finite sums force equality
    of the first components. *)
Lemma continuous_part_local_borel_restriction (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) (A B S : set X) :
  is_measure phi -> is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  (forall D, borel_set D -> measure_measurable psi D) ->
  borel_set B -> B `<=` A -> phi (A `\` B)=0 -> gamma A=psi B -> psi A< +oo ->
  borel_set S -> S `<=` A -> gamma S=psi (B `&` S).
Proof.
move=> hphi hpsi hg hb hB hBA hz heA hfinA hS hSA.
have hgamma := @continuous_part_is_measure R X phi psi gamma hphi hpsi hg.
have hSm := @continuous_part_borel_measurable R X phi psi gamma hphi hpsi hg hb S hS.
have hlow : gamma S<=psi (B `&` S).
  apply: (@continuous_part_lower R X phi psi gamma hg S (B `&` S)).
  - exact: (@borel_family_binary_intersection _ setT _ (borel_sets_family X) B S hB hS).
  - apply: (@measure_null_subset R X phi hphi _ (A `\` B)) hz.
    move=> x [hx hn]; split; first exact: hSA x hx.
    move=> hbx; apply: hn; by split.
have hcomp : gamma (A `\` S)<=psi (B `\` S).
  apply: (@continuous_part_lower R X phi psi gamma hg (A `\` S) (B `\` S)).
  - exact: borel_set_difference hB hS.
  - apply: (@measure_null_subset R X phi hphi _ (A `\` B)) hz.
    move=> x [[hx hns] hn]; split=> // hbx; apply: hn; by split.
have hAS : A `&` S=S.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hSA x hx.
have hegamma := hSm A; rewrite hAS in hegamma.
have hepsi := hb S hS B.
have hgammaAfin : gamma A< +oo.
  rewrite heA; exact: le_lt_trans (@measure_mono R X psi hpsi B A hBA) hfinA.
have hcompfin : gamma (A `\` S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hgamma _)).
  apply: le_lt_trans _ hgammaAfin.
  apply: (@measure_mono R X gamma hgamma)=> x []; by [].
have hsum := leeD2l (psi (B `&` S)) hcomp.
rewrite -hepsi -heA hegamma (@leeD2rE R (gamma (A `\` S)) (psi (B `&` S)) (gamma S) hcompfin) in hsum.
apply/eqP; by rewrite eq_le hlow hsum.
Qed.

(** Source for [continuous_part_local_restriction]: the full local identity
    psi_phi(S)=psi(B intersection S) for every S subset A in Federer 2.9.2,
    p. 153 Finite phi(A) and psi(A) justify the two common hulls and the
    finite cancellation. No measurability of S is assumed. *)
Theorem continuous_part_local_restriction (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) (A : set X) :
  is_measure phi -> is_measure psi -> is_borel_regular_measure phi -> is_borel_regular_measure psi ->
  is_absolutely_continuous_part phi psi gamma -> borel_set A -> phi A< +oo -> psi A< +oo ->
  exists B, borel_set B /\ B `<=` A /\ phi (A `\` B)=0 /\
    forall S, S `<=` A -> gamma S=psi (B `&` S).
Proof.
move=> hphi hpsi hrphi hrpsi hg hA hphiA hpsiA.
have hbphi D : borel_set D -> measure_measurable phi D :=
  @borel_regular_borel_measurable R X phi hphi hrphi D.
have hbpsi D : borel_set D -> measure_measurable psi D :=
  @borel_regular_borel_measurable R X psi hpsi hrpsi D.
have [B [hB [hBA [hz heA]]]] := @continuous_part_attained_inside R X phi psi gamma A A
  hphi hpsi hg hA (fun x hx => hx).
exists B; split=> //; split=> //; split=> // S hSA.
have [T [hT [hST [hTA [hephi hepsi]]]]] := @common_borel_hull_inside R X phi psi A S
  hphi hpsi hrphi hrpsi hA hSA.
have hphiS : phi S< +oo := le_lt_trans (@measure_mono R X phi hphi S A hSA) hphiA.
have hpsiS : psi S< +oo := le_lt_trans (@measure_mono R X psi hpsi S A hSA) hpsiA.
have hphiH := @measure_hull_of_finite_equal_measure R X phi hphi S T hST (hbphi T hT) hephi hphiS.
have hpsiH := @measure_hull_of_finite_equal_measure R X psi hpsi S T hST (hbpsi T hT) hepsi hpsiS.
have hegamma := @continuous_part_on_phi_hull R X phi psi gamma S T hphi hg hbphi hphiH.
have heT := @continuous_part_local_borel_restriction R X phi psi gamma A B T
  hphi hpsi hg hbpsi hB hBA hz heA hpsiA hT hTA.
have heB := @measure_hull_test R X psi S T hpsiH B (hbpsi B hB).
by rewrite hegamma heT -heB.
Qed.
