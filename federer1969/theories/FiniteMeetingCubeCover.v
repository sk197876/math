(** Federer (1969), 3.2.38, p. 274: retain just the finitely
    many grid cells meeting the original compact source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws
  EqualCoordinateCubeGridMeasure EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_meeting_coordinate_grid_cover]: the family F
    of actual compact cubes meeting C in Federer 3.2.38, p. 274.
    A finite subtype retains exactly those original grid cells.
    Null overlaps are inherited through the injective index inclusion;
    empty original sources yield an empty index type. The source itself
    need not be measurable for this purely geometric filtering step. *)
Lemma finite_meeting_coordinate_grid_cover (R:realType) n k (a:R_n R n) (h:R)
    (Q:coordinate_cube_grid_indices n k->set (inner_metric_space (@euclidean_inner_productP R n)))
    (C:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_equal_coordinate_cube_grid k a h Q ->C `<=` \bigcup_s Q s ->
  exists (I:finType) (b:I->R_n R n)
    (P:I->set (inner_metric_space (@euclidean_inner_productP R n))),
    [ /\forall i,is_euclidean_coordinate_cube (b i) h (P i),
      forall i,(P i `&` C)!=set0,
      C `<=` \bigcup_i P i &
      forall i j,i!=j ->@euclidean_lebesgue_measure R n (P i `&` P j)=0%E].
Proof.
move=>hQ hCover.
pose F:set (coordinate_cube_grid_indices n k):=[set s|(Q s `&` C)!=set0].
pose I:=[the finType of set_type F].
pose b (i:I):R_n R n:=[ffun j=>a j+((val i) j)%:R*h].
pose P (i:I):=Q (val i).
exists I,b,P; split.
- move=>i; exact:equal_coordinate_grid_cell_cube hQ (val i).
- move=>i; exact:(set_valP i).
- move=>x hx; have [s _ hs]:=hCover x hx.
  have hF:F s by exists x; split.
  exists (exist _ s (mem_set hF):I)=>//.
- move=>i j hij.
  have hNe:val i!=val j.
    apply/eqP=>he; apply:(elimN eqP hij); exact:val_inj he.
  exact:(@equal_coordinate_grid_null_overlaps R n k a h Q hQ (val i) (val j) hNe).
Qed.
