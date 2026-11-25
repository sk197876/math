(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:sv and lem:sv items hom and lip: the public number
      sv_m(X) = sup { inf { |X(v)| : v in P, |v| = 1 } : P in G(V,m) }
    for X in Hom(V,W), with V of dimension n and 1 <= m <= n, its
    elementary bounds, homogeneity and Lipschitz continuity with respect
    to the operator norm (Federer 1.7.6). All proofs use the sealed
    characteristic property. Items rank and eigen and rem:sv_singular are
    in DgprSingularValueRank.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities LinearBasis Hom
  OperatorNorm HomInner HomOperatorNorm ModuleQuotient GrassmannSubspaces.
From DPGPR Require Import DgprSingularValueUP DgprSingularValueSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Interface.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m <= n)%N.

(** Source for [dgpr_sv]: blueprint def:sv, the number sv_m(X), read
    from the sealed interface. *)
Definition dgpr_sv (X : Hom V W) : R := @DgprSingularValue.value R V W B C hB hC n e he m hm X.

(** Source for [dgpr_svP]: blueprint def:sv, sv_m(X) satisfies the
    characteristic property of the supremum. *)
Theorem dgpr_svP (X : Hom V W) : is_dgpr_sv hB hC m X (dgpr_sv X).
Proof. exact: DgprSingularValue.laws. Qed.

(** Source for [dgpr_sv_characterisation]: blueprint def:sv, every
    number with the characteristic property equals sv_m(X). *)
Lemma dgpr_sv_characterisation (X : Hom V W) s : is_dgpr_sv hB hC m X s -> dgpr_sv X = s.
Proof. move=> h; exact: dgpr_sv_unique (dgpr_svP X) h. Qed.

(** Source for [dgpr_sv_lower]: blueprint def:sv, for P in G(V,m),
    every lower bound of { |X(v)| : v in P, |v| = 1 } is at most
    sv_m(X). *)
Lemma dgpr_sv_lower (X : Hom V W) (P : G V m) t :
  (forall v, grassmann_val P v -> inner_norm hB v = 1 -> t <= inner_norm hC (X v)) ->
  t <= dgpr_sv X.
Proof. move=> h; exact: (dgpr_sv_upper (dgpr_svP X) (P := P) h). Qed.

(** Source for [dgpr_sv_approximate]: blueprint def:sv, every r below
    sv_m(X) is a lower bound of { |X(v)| : v in P, |v| = 1 } for some
    P in G(V,m). *)
Lemma dgpr_sv_approximate (X : Hom V W) r : r < dgpr_sv X ->
  exists P : G V m, forall v, grassmann_val P v -> inner_norm hB v = 1 ->
    r <= inner_norm hC (X v).
Proof. move=> h; exact: dgpr_sv_least (dgpr_svP X) r h. Qed.

(** Source for [dgpr_sv_nonnegative]: blueprint def:sv, 0 <= sv_m(X). *)
Lemma dgpr_sv_ge0 (X : Hom V W) : 0 <= dgpr_sv X.
Proof. exact: dgpr_sv_nonnegative (dgpr_svP X). Qed.

(** Source for [dgpr_sv_le_operator_norm]: blueprint proof of lem:KF,
    sv_m(X) <= ||X||, the operator norm of Federer 1.7.6. *)
Lemma dgpr_sv_le_operator_norm (X : Hom V W) :
  dgpr_sv X <= linear_operator_norm hB hC he (hom_as_linear X).
Proof.
have /andP [hm0 _] := hm.
apply: (dgpr_sv_upper_bound (dgpr_svP X)) => P.
have [v [hv hv1]] := dgpr_grassmann_unit_vector hB P hm0.
exists v; split=> //; split=> //.
have := linear_operator_norm_bound hB hC he (hom_as_linear X) v.
by rewrite hom_as_linearE hv1 mulr1.
Qed.

(** Source for [dgpr_sv_le_hom_norm]: blueprint proof of lem:KF,
    sv_m(X) <= ||X|| <= |X| by Federer 1.7.9, p. 35. *)
Lemma dgpr_sv_le_hom_norm (X : Hom V W) : dgpr_sv X <= hom_norm hB hC he X.
Proof.
apply: le_trans (dgpr_sv_le_operator_norm X) _.
exact: (hom_operator_norm_comparison hB hC he X).1.
Qed.

(** Source for [dgpr_sv_hom]: blueprint lem:sv item hom,
    sv_m(cX) = |c| sv_m(X). *)
Theorem dgpr_sv_hom (X : Hom V W) (c : R) : dgpr_sv (c *: X) = `|c| * dgpr_sv X.
Proof.
have /andP [hm0 _] := hm.
apply: dgpr_sv_characterisation; exact: dgpr_sv_scale hm0 (dgpr_svP X).
Qed.

(** Source for [dgpr_sv_lip]: blueprint lem:sv item lip,
    |sv_m(X) - sv_m(X')| <= ||X - X'||, the operator norm of
    Federer 1.7.6. *)
Theorem dgpr_sv_lip (X X' : Hom V W) :
  `|dgpr_sv X - dgpr_sv X'| <= linear_operator_norm hB hC he (hom_as_linear (X - X')).
Proof.
pose d := linear_operator_norm hB hC he (hom_as_linear (X - X')).
have hd v : inner_norm hB v = 1 -> inner_norm hC ((X - X') v) <= d.
  move=> hv1; have := linear_operator_norm_bound hB hC he (hom_as_linear (X - X')) v.
  by rewrite hom_as_linearE hv1 mulr1.
have hXv v : (X - X') v = X v - X' v by rewrite hom_addE.
have h1 : dgpr_sv X <= dgpr_sv X' + d.
  apply: (dgpr_sv_compare (dgpr_svP X) (dgpr_svP X')) => v hv1.
  have -> : X v = X' v + (X - X') v by rewrite hXv addrC subrK.
  apply: le_trans (inner_norm_triangle hC _ _) _; by rewrite lerD2l hd.
have h2 : dgpr_sv X' <= dgpr_sv X + d.
  apply: (dgpr_sv_compare (dgpr_svP X') (dgpr_svP X)) => v hv1.
  have -> : X' v = X v + - (X - X') v by rewrite hXv opprB addrC subrK.
  apply: le_trans (inner_norm_triangle hC _ _) _; by rewrite inner_normN lerD2l hd.
rewrite ler_distl; apply/andP; split; last by [].
by rewrite lerBlDr.
Qed.
End Interface.

(** Source for [dgpr_sv_basis_independent]: blueprint def:sv, the
    number depends only on the inner products, m and X, not on the basis
    or the proofs used to obtain it. *)
Lemma dgpr_sv_basis_independent (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) n' (e' : 'I_n' -> V) (he' : is_basis e')
    m (hm : (0 < m <= n)%N) (hm' : (0 < m <= n')%N) (X : Hom V W) :
  dgpr_sv hB hC he hm X = dgpr_sv hB hC he' hm' X.
Proof. exact: dgpr_sv_unique (dgpr_svP hB hC he hm X) (dgpr_svP hB hC he' hm' X). Qed.
