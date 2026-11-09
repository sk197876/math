(** Federer (1969), 3.4.2(7), pp. 312–313: class reduction in Ω. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanSubmanifoldUP
  NormDiffeomorphismUP NormDiffeomorphismClass NormRegularity
  EuclideanProjectionSpace CriticalManifoldFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_submanifold_lower_class]: supporting the
    class reduction in the induction of 3.4.2(7), pp. 312–313.
    Lowering class preserves the original straightening charts and
    their inverse and image laws, by 3.1.19, p. 231. *)
Lemma critical_submanifold_lower_class (R:realType) m mu k j (S:set (R_n R m)):
  (j<=k)%N ->is_euclidean_submanifold mu k S ->is_euclidean_submanifold mu j S.
Proof.
move=>hjk hS x hx.
have [U [V [f [g [Z hChart]]]]]:=hS x hx.
exists U,V,f,g,Z.
have [hU hD hImage]:=hChart;constructor=>//.
exact:(norm_diffeomorphism_lower hjk hD).
Qed.

(** Source for [critical_manifold_chart_lower_class]: the same
    original projection and inverse chart remain admissible after
    lowering class, as used in 3.4.2(7), pp. 312–313. *)
Lemma critical_manifold_chart_lower_class (R:realType) m mu k j Z S
    (p:euclidean_projection_space R m mu) g:
  (j<=k)%N ->is_critical_manifold_chart k Z S p g ->
  is_critical_manifold_chart j Z S p g.
Proof.
move=>hjk [hKernel hConvex hOpen hClass hLeft hRight];constructor=>//.
exact:(norm_class_lower hjk hClass).
Qed.

(** Source for [critical_manifold_family_lower_class]: Ω(mu,k)
    is contained in Ω(mu,j) for 1<=j<=k, supporting the induction
    in 3.4.2(7), pp. 312–313. The dimension-zero alternative remains. *)
Lemma critical_manifold_family_lower_class (R:realType) m d Z mu k j S:
  (0<j)%N ->(j<=k)%N ->@critical_manifold_family R m d Z mu k S ->
  @critical_manifold_family R m d Z mu j S.
Proof.
move=>hj hjk [hMu [hk [hS hAlternative]]].
split;first exact:hMu.
split;first exact:hj.
split;first exact:(critical_submanifold_lower_class hjk hS).
case:hAlternative=>[hZero|[p [g hChart]]];first by left.
right;exists p,g;exact:(critical_manifold_chart_lower_class hjk hChart).
Qed.
