(** Federer (1969), 4.1.11, p. 366: every original
    m-simplex in R^n is an affine current image of
    any prescribed nondegenerate m-simplex in R^m.
    The preceding vertex interpolation and the original
    simplex naturality theorem give the exact current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import AffineMaps GrassmannAbbreviations CurrentSpaces
  CurrentJoinAffineSourcePushforward CurrentSimplexFrame OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_simplex_current_parametrisation]:
    the original affine image of any nondegenerate source
    m-simplex gives the prescribed target simplex, Federer
    4.1.11, p. 366. The target may be degenerate and
    the case m=0 is retained. *)
Theorem oriented_simplex_current_parametrisation (R:realType) (h2:(1+1:R)!=0) m n
    (w:'I_(m.+1)->R_n R m) (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex w->
  exists A:R_n R m->R_n R n,exists hA:is_affine_map A,
    @current_join_affine_current R h2 m n A hA m (@OrientedSimplexCurrent.value R h2 m m w)
      (@oriented_simplex_current_compact R h2 m m w)=@OrientedSimplexCurrent.value R h2 n m v.
Proof.
move=>hW;have[A [hA hVertices]]:=@current_simplex_affine_vertices_exists R m n w v hW.
exists A,hA.
have hImage:=@oriented_simplex_current_affine R h2 m n A hA m w
  (@oriented_simplex_current_compact R h2 m m w).
have hV:(fun k=>A (w k))=v by apply:funext=>k;exact:hVertices.
by rewrite hV in hImage.
Qed.

(** Source for [oriented_simplex_current_standard_parametrisation]:
    in particular every original simplex is the affine
    image of the standard source simplex, supporting
    Federer's orientation and prism proofs in 4.1.11,
    p. 366. This is the preceding arbitrary-source theorem. *)
Theorem oriented_simplex_current_standard_parametrisation (R:realType) (h2:(1+1:R)!=0) m n
    (v:'I_(m.+1)->R_n R n):
  exists A:R_n R m->R_n R n,exists hA:is_affine_map A,
    @current_join_affine_current R h2 m n A hA m
      (@OrientedSimplexCurrent.value R h2 m m (@current_standard_simplex_vertices R m))
      (@oriented_simplex_current_compact R h2 m m (@current_standard_simplex_vertices R m))=
      @OrientedSimplexCurrent.value R h2 n m v.
Proof.
exact:(@oriented_simplex_current_parametrisation R h2 m n
  (@current_standard_simplex_vertices R m) v (@current_standard_simplex_nondegenerate R m)).
Qed.
