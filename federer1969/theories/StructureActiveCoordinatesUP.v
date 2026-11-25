(** Federer (1969), 3.3.4, p. 290:
    independent coordinate laws for the active
    space spanned by one normal axis and
    the first m frame vectors. Coordinates
    put the distinguished normal axis first. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_structure_active_inclusion]:
    the original (m+1)-dimensional X of
    Federer 3.3.4, p. 290, before
    rotating the full ambient frame. The
    first active coordinate is g_j and
    the remaining ones are g_1,...,g_m;
    every other normal coordinate is zero. *)
Definition is_structure_active_inclusion (R:realType) m k (j:'I_k)
    (w:Hom (R_n R (1+m)) (R_n R (m+k))):=
  forall u,@euclidean_first_block R m k (w u)=@euclidean_last_block R 1 m u /\
    forall l,(@euclidean_last_block R m k (w u)) l=
      if l==j then u (lshift m (ord0:'I_1)) else 0.
