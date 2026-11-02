(** Federer (1969), 3.2.28, printed pp. 263–267:
    class-infinity submanifolds in the suitable Euclidean
    ambient spaces. The same charts and inverse maps
    work at every finite derivative order. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations GrassmannSubspaces
  EuclideanSubmanifoldUP FiniteInnerChartUP FiniteInnerSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_smooth_submanifold]: class infinity
    in Federer 3.2.28, pp. 263–267, using the
    straightening definition of 3.1.19, p. 231.
    A single local chart and inverse have every finite class. *)
Definition is_euclidean_smooth_submanifold (R:realType) n mu (B:set (R_n R n)):=
  forall b,B b ->exists (T C:set (R_n R n)) (s t:R_n R n->R_n R n)
    (Z:G (R_n R n) mu),forall k,
      is_submanifold_straightening k B b T C s t Z.

(** Source for [is_inner_smooth_submanifold]: class infinity
    in the actual finite inner-product ambient spaces of
    Federer 3.2.28, pp. 263–267. The ambient
    isometry and the local smooth charts are chosen only
    inside the required existence assertions. *)
Definition is_inner_smooth_submanifold (R:realType) (V:lmodType R)
    (B:V->V->R) mu (S:set V):=
  exists n (e:Hom (R_n R n) V) (p:Hom V (R_n R n)),
    is_finite_inner_chart B e p /\
    @is_euclidean_smooth_submanifold R n mu (p @` S).

(** Source for [euclidean_smooth_submanifold_class]: class
    infinity gives each finite class using the same charts,
    Federer 3.2.28, pp. 263–267. *)
Lemma euclidean_smooth_submanifold_class (R:realType) n mu (B:set (R_n R n)):
  @is_euclidean_smooth_submanifold R n mu B ->forall k,
    @is_euclidean_submanifold R n mu k B.
Proof.
move=>h k b hb; have [T [C [s [t [Z hChart]]]]]:=h b hb.
exists T,C,s,t,Z; exact:hChart.
Qed.

(** Source for [inner_smooth_submanifold_class]: the same
    ambient isometry and local charts give every finite class,
    supporting Federer 3.2.28, pp. 263–267. *)
Lemma inner_smooth_submanifold_class (R:realType) (V:lmodType R)
    (B:V->V->R) mu (S:set V):
  is_inner_smooth_submanifold B mu S ->forall k,is_inner_submanifold B mu k S.
Proof.
move=>[n [e [p [hChart hSmooth]]]] k.
exists n,e,p; split=>//; exact:euclidean_smooth_submanifold_class hSmooth k.
Qed.
