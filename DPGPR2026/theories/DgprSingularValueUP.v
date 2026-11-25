(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:sv: for X in Hom(V,Y) the number
      sv_m(X) = sup { inf { |X(v)| : v in P, |v| = 1 } : P in G(V,m) },
    where G(V,m) is Federer's Grassmannian of m dimensional subspaces
    (Federer 1.6.2). This file states the characteristic property of the
    supremum and derives from it alone uniqueness, homogeneity and the
    comparison used for the Lipschitz estimate of lem:sv. The number is
    chosen in DgprSingularValueSealed.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization LinearBasis Hom
  ModuleQuotient SubspaceCarrier GrassmannSubspaces FiniteIndependence FiniteSpans
  FiniteSpanSpace SimplexAffinePlaneUnivalence FiniteBasisComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Grassmann.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [dgpr_grassmann_unit_vector]: blueprint def:sv, Federer
    1.6.2, p. 24: for 1 <= m every P in G(V,m) contains a unit vector,
    so the infimum in def:sv is taken over a nonempty set. *)
Lemma dgpr_grassmann_unit_vector m (P : G V m) :
  (0 < m)%N -> exists v, grassmann_val P v /\ inner_norm hB v = 1.
Proof.
move=> hm; have [b hb] := grassmann_proof P.
pose i := Ordinal hm; pose w := subspace_val (b i).
have hw : w != 0.
  apply/negP => /eqP hw0.
  have hc : \sum_j (if j == i then (1 : R) else 0) *: b j = 0.
    rewrite (bigD1 i) //= ?eqxx scale1r big1 ?addr0.
    + by apply: val_inj; exact: hw0.
    + by move=> j hj; rewrite (negbTE hj) scale0r.
  have := finite_basis_independent hb hc i.
  by rewrite eqxx => /eqP; rewrite oner_eq0.
exists (inner_normalize hB w); split; last exact: inner_normalize_norm.
apply: subspace_scale; exact: subspace_valP.
Qed.

(** Source for [dgpr_grassmann_nonempty]: blueprint def:sv with
    1 <= m <= n: the span of m members of a basis of V belongs to
    G(V,m) (Federer 1.6.1, 1.6.2). *)
Lemma dgpr_grassmann_nonempty n (e : 'I_n -> V) m :
  is_basis e -> (m <= n)%N -> exists P : G V m, True.
Proof.
move=> he hmn.
pose f := fun i : 'I_m => e (widen_ord hmn i).
have hf : finite_independent f.
  have he' : finite_independent e := finite_basis_independent he.
  exact: (finite_independent_widen (h:=hmn) he').
exists (@GrassmannSubspace R V m (finite_span_subspace f)
  (ex_intro _ (finite_span_basis f) (finite_span_basisP hf))).
done.
Qed.
End Grassmann.

Section Predicate.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable m : nat.

(** Source for [dgpr_sv_lower_bound]: blueprint def:sv: t is a lower
    bound of { |X(v)| : v in P, |v| = 1 }, that is, t does not exceed
    the infimum appearing in def:sv. *)
Definition dgpr_sv_lower_bound (X : Hom V W) (P : G V m) (t : R) :=
  forall v, grassmann_val P v -> inner_norm hB v = 1 -> t <= inner_norm hC (X v).

(** Source for [is_dgpr_sv]: blueprint def:sv: s is the least upper
    bound of the infima inf { |X(v)| : v in P, |v| = 1 } over
    P in G(V,m). Since every lower bound of such a set is at most its
    infimum, s bounds every lower bound of every P, and every r < s is
    a lower bound for some P. *)
Record is_dgpr_sv (X : Hom V W) (s : R) : Prop := {
  dgpr_sv_upper : forall P t, dgpr_sv_lower_bound X P t -> t <= s;
  dgpr_sv_least : forall r, r < s -> exists P, dgpr_sv_lower_bound X P r
}.

(** Source for [dgpr_sv_lower_bound_mono]: blueprint def:sv, a smaller
    number is again a lower bound. *)
Lemma dgpr_sv_lower_bound_mono X P t t' :
  t' <= t -> dgpr_sv_lower_bound X P t -> dgpr_sv_lower_bound X P t'.
Proof. move=> htt h v hv hv1; exact: le_trans htt (h v hv hv1). Qed.

(** Source for [dgpr_sv_unique]: blueprint def:sv, the least upper
    bound is unique. *)
Lemma dgpr_sv_unique X s s' : is_dgpr_sv X s -> is_dgpr_sv X s' -> s = s'.
Proof.
have hlt (a b : R) : is_dgpr_sv X a -> is_dgpr_sv X b -> ~ b < a.
  move=> ha hb hba; have [hm1 hm2] := midf_lt hba.
  have [P hP] := dgpr_sv_least ha hm2.
  have := dgpr_sv_upper hb hP.
  by rewrite leNgt hm1.
move=> h h'; apply/eqP; rewrite eq_le; apply/andP; split.
- by rewrite leNgt; apply/negP => hh; exact: (hlt _ _ h h' hh).
- by rewrite leNgt; apply/negP => hh; exact: (hlt _ _ h' h hh).
Qed.

(** Source for [dgpr_sv_nonnegative]: blueprint def:sv, the number is
    nonnegative, because 0 bounds every set of lengths from below. *)
Lemma dgpr_sv_nonnegative X s : is_dgpr_sv X s -> 0 <= s.
Proof.
move=> h; have h1 : s - 1 < s by rewrite ltrBlDr ltrDl ltr01.
have [P _] := dgpr_sv_least h h1.
apply: (dgpr_sv_upper h (P := P)) => v _ _; exact: inner_norm_nonnegative.
Qed.

(** Source for [dgpr_sv_upper_bound]: blueprint def:sv and lem:KF: if
    every P in G(V,m) contains a unit vector v with |X(v)| <= M, then
    sv_m(X) <= M. *)
Lemma dgpr_sv_upper_bound X s M :
  is_dgpr_sv X s ->
  (forall P : G V m, exists v, grassmann_val P v /\ inner_norm hB v = 1 /\
    inner_norm hC (X v) <= M) -> s <= M.
Proof.
move=> h hM; rewrite leNgt; apply/negP => hMs.
have [hm1 hm2] := midf_lt hMs.
have [P hP] := dgpr_sv_least h hm2.
have [v [hv [hv1 hXv]]] := hM P.
have hle := le_trans (hP v hv hv1) hXv.
by move: hm1; rewrite ltNge hle.
Qed.

(** Source for [dgpr_sv_scale]: blueprint lem:sv item hom,
    sv_m(cX) = |c| sv_m(X), derived from the characteristic property.
    The hypothesis 1 <= m supplies a unit vector in each P. *)
Lemma dgpr_sv_scale X s c :
  (0 < m)%N -> is_dgpr_sv X s -> is_dgpr_sv (c *: X) (`|c| * s).
Proof.
move=> hm h; have [hc|hc] := eqVneq c 0.
- rewrite hc normr0 mul0r; constructor.
  + move=> P t hP; have [v [hv hv1]] := dgpr_grassmann_unit_vector hB P hm.
    have := hP v hv hv1; by rewrite hom_scaleE scale0r inner_norm0.
  + move=> r hr; have h1 : s - 1 < s by rewrite ltrBlDr ltrDl ltr01.
    have [P _] := dgpr_sv_least h h1.
    exists P => v _ _; rewrite hom_scaleE scale0r inner_norm0; exact: ltW.
have hc0 : 0 < `|c| by rewrite normr_gt0.
constructor.
- move=> P t hP; rewrite -ler_pdivrMl //.
  apply: (dgpr_sv_upper h (P := P)) => v hv hv1.
  rewrite ler_pdivrMl // -inner_normZ -hom_scaleE; exact: hP.
- move=> r hr; have hr' : r / `|c| < s by rewrite ltr_pdivrMr // mulrC.
  have [P hP] := dgpr_sv_least h hr'.
  exists P => v hv hv1; rewrite hom_scaleE inner_normZ -ler_pdivrMl // mulrC.
  exact: hP.
Qed.

(** Source for [dgpr_sv_compare]: blueprint lem:sv, proof of item lip:
    if |X(v)| <= |X'(v)| + d for every unit vector v, then
    sv_m(X) <= sv_m(X') + d. *)
Lemma dgpr_sv_compare X X' s s' d :
  is_dgpr_sv X s -> is_dgpr_sv X' s' ->
  (forall v, inner_norm hB v = 1 -> inner_norm hC (X v) <= inner_norm hC (X' v) + d) ->
  s <= s' + d.
Proof.
move=> h h' hd; rewrite leNgt; apply/negP => hlt.
have [hm1 hm2] := midf_lt hlt.
have [P hP] := dgpr_sv_least h hm2.
have hP' : dgpr_sv_lower_bound X' P ((s' + d + s) / 2 - d).
  move=> v hv hv1; rewrite lerBlDr; exact: le_trans (hP v hv hv1) (hd v hv1).
have := dgpr_sv_upper h' hP'; rewrite lerBlDr => hle.
by move: hm1; rewrite ltNge hle.
Qed.
End Predicate.
